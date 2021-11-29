// Package xmlwriter provides a lightweight XML encoder with basic namespace
// awareness and formatting.
//
// Unlike encoding/xml.Encoder, it supports self-closing tags, has a simpler
// interface, and provides more control over indentation and namespaces.
package xmlwriter

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"strings"
)

// NamespaceXML is the built-in namespace bound to the xml prefix.
const NamespaceXML NS = "http://www.w3.org/XML/1998/namespace"

// NamespaceMatcher represents the desired namespace for an element or
// attribute.
type NamespaceMatcher interface {
	uri() (NS, bool)
	prefix() (Prefix, bool)
}

// NS is a namespace URI. An empty URI is the empty namespace.
type NS string

func (n NS) uri() (NS, bool) {
	return n, true
}

func (n NS) prefix() (Prefix, bool) {
	return "", false
}

// Prefix is a namespace prefix. An empty prefix is the default namespace.
type Prefix string

func (p Prefix) uri() (NS, bool) {
	return "", false
}

func (p Prefix) prefix() (Prefix, bool) {
	return p, true
}

// BoundNS is a bound namespace. The zero value is the default empty namespace.
type BoundNS struct {
	URI    NS
	Prefix Prefix
}

func (n BoundNS) uri() (NS, bool) {
	return n.URI, true
}

func (n BoundNS) prefix() (Prefix, bool) {
	return n.Prefix, true
}

// XMLWriter generates XML. All errors are sticky and can be retrieved with
// (*XMLWriter).Err() or (*XMLWriter).Close().
type XMLWriter struct {
	w *bufio.Writer
	s []*state // nil until the first element of any kind is written
	e error    // sticky error
	i string   // indent string
}

type state struct {
	HasChildren  bool
	NoIndentNext bool // if the last child was an unindented text node or comment
	Name         string
	TagName      string
	Namespace    BoundNS
	Namespaces   []BoundNS // appended to the previous state's slice
	Attr         []string
}

// New creates a new *XMLWriter writing to w.
func New(w io.Writer) *XMLWriter {
	return &XMLWriter{
		w: bufio.NewWriter(w),
	}
}

// Indent sets the string used for indentation. If s is empty, the output is not
// indented.
func (w *XMLWriter) Indent(s string) {
	w.i = s
}

// BlankLine adds a blank line if indentation is enabled.
func (x *XMLWriter) BlankLine() error {
	return x.Text(true, "")
}

// DefaultProcInst adds the default XML processing instruction.
func (x *XMLWriter) DefaultProcInst() error {
	return x.ProcInst("xml", `version="1.0" encoding="UTF-8"`)
}

// Start starts a new element in ns (the current one if nil), defining the
// provided namespaces, if any. If indentation is enabled, and the current
// element is empty or its last child was not an unidented text node or comment,
// then a newline and the indentation is written before the opening tag.
func (x *XMLWriter) Start(ns NamespaceMatcher, name string, define ...BoundNS) error {
	if x.e != nil {
		return x.e
	}
	s := x.cur()
	for i, ns1 := range define {
		if ns1.Prefix != "" {
			if !isNameString(string(ns1.Prefix)) {
				x.e = fmt.Errorf("namespace %q prefix %q is not a valid xml name", ns1.URI, ns1.Prefix)
				return x.e
			}
			if ns1.URI == "" {
				x.e = fmt.Errorf("prefixed namespace %q must not have an empty URI", ns1.Prefix)
				return x.e
			}
		}
		for _, ns2 := range define[i+1:] {
			if ns1.Prefix == ns2.Prefix {
				x.e = fmt.Errorf("duplicate defined namespace prefix %q", ns1.Prefix)
				return x.e
			}
		}
	}
	var nss []BoundNS
	if s != nil {
		nss = append(s.Namespaces, define...)
	} else {
		nss = append([]BoundNS{{
			URI:    NamespaceXML,
			Prefix: "xml",
		}}, define...)
	}
	rns, err := resolveElementNS(ns, nss)
	if err != nil {
		x.e = fmt.Errorf("failed to validate namespace %q for element %q: %w", ns, name, err)
		return x.e
	}
	n, u := applyNS(rns, name)
	if s != nil {
		if !s.HasChildren {
			x.w.WriteByte('>')
		}
		if x.i != "" && !s.NoIndentNext {
			x.w.WriteByte('\n')
			for i := 0; i < len(x.s); i++ {
				x.w.WriteString(x.i)
			}
		}
	}
	x.w.WriteByte('<')
	x.w.WriteString(n)
	for _, ns := range define {
		if ns.URI != "" || s != nil { // all are empty by default on the root element
			x.w.WriteString(` xmlns`)
			if ns.Prefix != "" {
				x.w.WriteByte(':')
				x.w.WriteString(string(ns.Prefix))
			}
			x.w.WriteByte('=')
			x.w.WriteByte('"')
			escapeText(x.w, []byte(ns.URI), true)
			x.w.WriteByte('"')
		}
	}
	x.e = x.w.Flush()
	x.s = append(x.s, &state{
		Name:       u,
		TagName:    n,
		Namespace:  rns,
		Namespaces: nss,
	})
	if s != nil {
		s.HasChildren = true
		s.NoIndentNext = false
	}
	return x.e
}

// Attr adds an attribute in ns (the current one if nil) to the current element.
// If the element has children or the attribute has already been defined, an
// error is returned.
func (x *XMLWriter) Attr(ns NamespaceMatcher, name, value string) error {
	if x.e != nil {
		return x.e
	}
	s := x.cur()
	if s == nil {
		x.e = fmt.Errorf("no element to add attribute to")
		return x.e
	}
	rns, err := resolveAttrNS(ns, s.Namespaces, s.Namespace)
	if err != nil {
		x.e = fmt.Errorf("failed to resolve namespace %q for attribute %q: %w", ns, name, err)
		return x.e
	}
	n, u := applyNS(rns, name)
	if s.HasChildren {
		x.e = fmt.Errorf("cannot add attribute %q to element %q with children", n, s.Name)
		return x.e
	}
	for _, a := range s.Attr {
		if a == u {
			x.e = fmt.Errorf("cannot add duplicate attribute %q to element %q", n, s.Name)
			return x.e
		}
	}
	s.Attr = append(s.Attr, u)
	x.w.WriteByte(' ')
	x.w.WriteString(n)
	x.w.WriteByte('=')
	x.w.WriteByte('"')
	escapeText(x.w, []byte(value), true)
	x.w.WriteByte('"')
	x.e = x.w.Flush()
	return x.e
}

// Text adds a text node to the current element. If indentation is enabled,
// indent is true, and the current element is empty or its last child was not an
// unidented text node or comment, then a newline and the indentation is written
// before the text.
func (x *XMLWriter) Text(indent bool, text string) error {
	if x.e != nil {
		return x.e
	}
	s := x.cur()
	if s == nil {
		x.e = fmt.Errorf("no element to add text node to")
		return x.e
	}
	if !s.HasChildren {
		x.w.WriteByte('>')
	}
	if x.i != "" && !s.NoIndentNext && indent {
		x.w.WriteByte('\n')
		if text != "" {
			for i := 0; i < len(x.s); i++ {
				x.w.WriteString(x.i)
			}
		}
	}
	escapeText(x.w, []byte(text), false)
	x.e = x.w.Flush()
	s.HasChildren = true
	s.NoIndentNext = !indent
	return x.e
}

// Raw adds the provided XML as-is.
func (x *XMLWriter) Raw(xml []byte) error {
	if x.e != nil {
		return x.e
	}
	s := x.cur()
	if s != nil {
		if !s.HasChildren {
			x.w.WriteByte('>')
		}
	}
	x.w.Write(xml)
	x.e = x.w.Flush()
	if s != nil {
		s.HasChildren = true
	}
	return x.e
}

// End ends the current tag. If self is true, a self-closing tag is written and
// an error is returned if the element has children. If indentation is enabled,
// self is false, the current element contains children and its last child was
// not an unidented text node or comment, then a newline and the indentation is
// written before the closing tag. If the current element is the last one and
// indentation is enabled, a newline is written after the closing tag.
func (x *XMLWriter) End(self bool) error {
	if x.e != nil {
		return x.e
	}
	s := x.cur()
	if s == nil {
		x.e = fmt.Errorf("no element to close")
		return x.e
	}
	if self && s.HasChildren {
		x.e = fmt.Errorf("cannot self-close element %q with children", s.Name)
		return x.e
	}
	if s.HasChildren {
		if x.i != "" && !s.NoIndentNext {
			x.w.WriteByte('\n')
			for i := 1; i < len(x.s); i++ {
				x.w.WriteString(x.i)
			}
		}
	} else if !self {
		x.w.WriteByte('>')
	}
	if self {
		x.w.WriteByte('/')
		x.w.WriteByte('>')
	} else {
		x.w.WriteByte('<')
		x.w.WriteByte('/')
		x.w.WriteString(s.TagName)
		x.w.WriteByte('>')
	}
	if x.i != "" && len(x.s) == 1 {
		x.w.WriteByte('\n')
	}
	x.e = x.w.Flush()
	x.s = x.s[:len(x.s)-1]
	return x.e
}

// ProcInst adds a processing instruction. If indentation is enabled, and the
// current element is empty or its last child was not an unidented text node or
// comment, then a newline and the indentation is written before the
// instruction. If it does not have a parent and indentation is enabled, a
// newline is written after the closing tag.
func (x *XMLWriter) ProcInst(target, inst string) error {
	if x.e != nil {
		return x.e
	}
	if target == "xml" && x.s != nil {
		x.e = fmt.Errorf("xml processing instruction must be the first token")
		return x.e
	}
	if !isNameString(target) {
		x.e = fmt.Errorf("xml processing instruction target must be a valid xml name")
		return x.e
	}
	if strings.Contains(inst, "?>") {
		x.e = fmt.Errorf("xml processing instruction must not contain '?>'")
		return x.e
	}
	s := x.cur()
	if s != nil {
		if !s.HasChildren {
			x.w.WriteByte('>')
		}
		if x.i != "" && !s.NoIndentNext {
			x.w.WriteByte('\n')
			for i := 0; i < len(x.s); i++ {
				x.w.WriteString(x.i)
			}
		}
	}
	x.w.WriteByte('<')
	x.w.WriteByte('?')
	x.w.WriteString(target)
	if inst != "" {
		x.w.WriteByte(' ')
		x.w.WriteString(inst)
	}
	x.w.WriteByte('?')
	x.w.WriteByte('>')
	if x.i != "" && s == nil {
		x.w.WriteByte('\n')
	}
	x.e = x.w.Flush()
	if s != nil {
		s.HasChildren = true
		s.NoIndentNext = false
	} else if x.s == nil {
		x.s = make([]*state, 0)
	}
	return x.e
}

// Directive adds a directive. If indentation is enabled, and the current
// element is empty or its last child was not an unidented text node or comment
// then a newline and the indentation is written before the instruction. If it
// does not have a parent and indentation is enabled, a newline is written after
// the closing tag.
func (x *XMLWriter) Directive(dir []byte) error {
	if x.e != nil {
		return x.e
	}
	if !isValidDirective(dir) {
		x.e = fmt.Errorf("xml directive is invalid")
		return x.e
	}
	s := x.cur()
	if s != nil {
		if !s.HasChildren {
			x.w.WriteByte('>')
		}
		if x.i != "" && !s.NoIndentNext {
			x.w.WriteByte('\n')
			for i := 0; i < len(x.s); i++ {
				x.w.WriteString(x.i)
			}
		}
	}
	x.w.WriteByte('<')
	x.w.WriteByte('!')
	x.w.Write(dir)
	x.w.WriteByte('>')
	if x.i != "" && s == nil {
		x.w.WriteByte('\n')
	}
	x.e = x.w.Flush()
	if s != nil {
		s.HasChildren = true
		s.NoIndentNext = false
	} else if x.s == nil {
		x.s = make([]*state, 0)
	}
	return x.e
}

// Comment adds a comment. If indentation is enabled, indent is true, and the
// current element is empty or its last child was not an unidented text node or
// comment, then a newline and the indentation is written before the comment. If
// it does not have a parent and indentation is enabled, a newline is written
// after the closing tag.
func (x *XMLWriter) Comment(indent bool, comment string) error {
	if x.e != nil {
		return x.e
	}
	if strings.Contains(comment, "-->") {
		x.e = fmt.Errorf("xml comment must not contain '-->'")
		return x.e
	}
	s := x.cur()
	if s != nil {
		if !s.HasChildren {
			x.w.WriteByte('>')
		}
		if x.i != "" && indent && !s.NoIndentNext {
			x.w.WriteByte('\n')
			for i := 0; i < len(x.s); i++ {
				x.w.WriteString(x.i)
			}
		}
	}
	x.w.WriteByte('<')
	x.w.WriteByte('!')
	x.w.WriteByte('-')
	x.w.WriteByte('-')
	x.w.WriteString(comment)
	x.w.WriteByte('-')
	x.w.WriteByte('-')
	x.w.WriteByte('>')
	if x.i != "" && s == nil {
		x.w.WriteByte('\n')
	}
	x.e = x.w.Flush()
	if s != nil {
		s.HasChildren = true
		s.NoIndentNext = !indent
	} else if x.s == nil {
		x.s = make([]*state, 0)
	}
	return x.e
}

func (x *XMLWriter) cur() *state {
	if i := len(x.s) - 1; i != -1 {
		return x.s[i]
	}
	return nil
}

// Err checks for an error.
func (x *XMLWriter) Err() error {
	return x.e
}

// Close checks for an error or unclosed elements. The writer cannot be used
// afterwards.
func (x *XMLWriter) Close() (err error) {
	if x.e != nil {
		err = x.e
	} else if len(x.s) != 0 {
		err = errors.New("unclosed elements remaining")
	}
	x.e = errors.New("already closed")
	return
}

func applyNS(ns BoundNS, name string) (string, string) {
	if ns.Prefix == "" {
		return name, string(ns.URI) + " " + name
	}
	if !isNameString(string(ns.Prefix)) {
		panic("invalid namespace prefix")
	}
	return string(ns.Prefix) + ":" + name, string(ns.URI) + " " + name
}

func resolveElementNS(ns NamespaceMatcher, nss []BoundNS) (BoundNS, error) {
	return resolveNS(ns, nss, false, BoundNS{})
}

func resolveAttrNS(ns NamespaceMatcher, nss []BoundNS, elementNS BoundNS) (BoundNS, error) {
	return resolveNS(ns, nss, true, elementNS)
}

func resolveNS(ns NamespaceMatcher, nss []BoundNS, isAttr bool, elementNS BoundNS) (BoundNS, error) {
	// current namespace
	if ns == nil {
		ns = Prefix("")
	}

	// match by prefix, then verify the uri if provided
	if prefix, ok := ns.prefix(); ok {
		// prefix must be a valid xml name
		if prefix != "" && !isNameString(string(prefix)) {
			return BoundNS{}, fmt.Errorf("namespace prefix %q is not a valid xml name", prefix)
		}
		// the default namespace for an attr is the element namespace
		if isAttr && prefix == "" {
			if uri, ok := ns.uri(); ok && uri != elementNS.URI {
				return BoundNS{}, fmt.Errorf("wanted default namespace to be %q, got %q", uri, elementNS.URI)
			}
			return BoundNS{elementNS.URI, ""}, nil
		}
		// search upwards for a matching prefix
		for i := len(nss) - 1; i >= 0; i-- {
			if nss[i].Prefix != prefix {
				continue
			}
			if uri, ok := ns.uri(); ok && uri != nss[i].URI {
				return BoundNS{}, fmt.Errorf("wanted namespace prefix %q to be %q, got %q", prefix, uri, nss[i].URI)
			}
			return BoundNS{nss[i].URI, prefix}, nil
		}
		return BoundNS{}, fmt.Errorf("namespace prefix %q is not defined", prefix)
	}

	// match by uri
	if uri, ok := ns.uri(); ok {
		// the default namespace for an attr is the element namespace
		if isAttr && elementNS.URI == uri {
			return BoundNS{elementNS.URI, ""}, nil
		}
		// search upwards for a unshadowed prefix matching the uri
		seen := map[Prefix]struct{}{}
		if isAttr {
			seen[Prefix("")] = struct{}{}
		}
		for i := len(nss) - 1; i >= 0; i-- {
			if _, ok := seen[nss[i].Prefix]; ok {
				continue
			}
			seen[nss[i].Prefix] = struct{}{}
			if nss[i].URI == uri {
				return nss[i], nil
			}
		}
		return BoundNS{}, fmt.Errorf("failed to find namespace prefix for %q", uri)
	}

	// neither uri nor prefix
	panic("namespace matcher does not match by prefix or uri")
}
