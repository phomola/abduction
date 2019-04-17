// Copyright 2018-2019 Petr Homola. All rights reserved.
// Use of this source code is governed by the AGPL v3.0
// that can be found in the LICENSE file.

package abduction

import (
	"fmt"
	"sort"
	"strings"

	"abduction/sat" //"github.com/phomola/abduction/sat"
)

type Term struct {
	Name string
	Args []string
}

func NewTerm(s ...string) *Term {
	return &Term{s[0], s[1:]}
}

func (t1 *Term) Unify(t2 *Term, vars map[string]string, cb func()) {
	var newVars []string
	if t1.Name == t2.Name && len(t1.Args) == len(t2.Args) {
		for i := 0; i < len(t1.Args); i++ {
			a1 := t1.Args[i]
			a2 := t2.Args[i]
			if a1[0] == '$' {
				if a, ok := vars[a1]; ok {
					if a != a2 {
						goto rollback
					}
				} else {
					vars[a1] = a2
					newVars = append(newVars, a1)
				}
			} else {
				if a1 != a2 {
					goto rollback
				}
			}
		}
		cb()
	}
rollback:
	for _, v := range newVars {
		delete(vars, v)
	}
}

func (t *Term) Subst(vars map[string]string) (*Term, bool) {
	ground := true
	var args []string
	for _, a1 := range t.Args {
		if a1[0] == '$' {
			if a2, ok := vars[a1]; ok {
				args = append(args, a2)
			} else {
				args = append(args, a1)
				ground = false
			}
		} else {
			args = append(args, a1)
		}
	}
	return &Term{t.Name, args}, ground
}

func (t *Term) SubstNoUids(vars map[string]string) (*Term, bool) {
	ground := true
	var args []string
	for _, a1 := range t.Args {
		if a1[0] == '$' {
			if len(strings.Split(a1, "#")) == 2 {
				args = append(args, a1)
			} else {
				if a2, ok := vars[a1]; ok {
					args = append(args, a2)
				} else {
					args = append(args, a1)
					ground = false
				}
			}
		} else {
			args = append(args, a1)
		}
	}
	return &Term{t.Name, args}, ground
}

func (t *Term) String() string {
	s := t.Name
	if len(t.Args) > 0 {
		s += "(" + strings.Join(t.Args, ",") + ")"
	}
	return s
}

type Rule struct {
	Ante []*Term
	Cons []*RuleConsTerm
}

func (r *Rule) backchain(i int, atoms *AtomSet, vars map[string]string, level int, maxLevel int, cb func()) {
	if i == len(r.Cons) {
		if level == maxLevel {
			for v, list := range vars {
				comps := strings.Split(v[1:], "+")
				if len(comps) == 2 {
					v1, v2 := "$"+comps[0], "$"+comps[1]
					if _, ok := vars[v1]; ok {
						panic("variable in a concatenation must be free")
					}
					if _, ok := vars[v2]; ok {
						panic("variable in a concatenation must be free")
					}
					comps := strings.Split(list, "+")
					for i := 1; i < len(comps); i++ {
						list1, list2 := comps[:i], comps[i:]
						vars[v1] = strings.Join(list1, "+")
						vars[v2] = strings.Join(list2, "+")
						cb()
					}
					delete(vars, v1)
					delete(vars, v2)
					goto end
				}
			}
			cb()
		end:
		}
	} else {
		atoms.Enumerate(func(a *Term, l int) {
			maxLevel2 := maxLevel
			if l > maxLevel2 {
				maxLevel2 = l
			}
			r.Cons[i].Term.Unify(a, vars, func() {
				r.backchain(i+1, atoms, vars, level, maxLevel2, cb)
			})
		})
	}
}

func (r *Rule) Backchain(atoms *AtomSet, vars map[string]string, level int, cb func()) {
	r.backchain(0, atoms, vars, level, 0, cb)
}

func (r *Rule) String() string {
	s := ""
	for _, t := range r.Ante {
		s += t.String() + " "
	}
	s += "->"
	for _, t := range r.Cons {
		s += " " + t.String()
	}
	return s
}

type TermLevel struct {
	Term  *Term
	Level int
}

type AtomSet struct {
	Atoms []TermLevel
}

func NewAtomSet() *AtomSet {
	return &AtomSet{}
}

func (as *AtomSet) Add(t *Term, level int) {
	for _, tl := range as.Atoms {
		if t.String() == tl.Term.String() {
			// fmt.Println("## duplicate:", t)
			return
		}
	}
	as.Atoms = append(as.Atoms, TermLevel{t, level})
}

func (as *AtomSet) Enumerate(cb func(*Term, int)) {
	for _, tl := range as.Atoms {
		cb(tl.Term, tl.Level)
	}
}

func (as *AtomSet) String() string {
	s := ""
	as.Enumerate(func(t *Term, l int) {
		s += t.String() + "\n"
	})
	return s
}

type RuleConsTerm struct {
	Term      *Term
	Exclusive bool
}

func (t *RuleConsTerm) String() string {
	return t.Term.String()
}

type RuleSignature struct {
	RuleId string
	Ante   []*Term
	Cons   []*RuleConsTerm
}

func NewRuleSignature(id int, ante []*Term, cons []*RuleConsTerm) *RuleSignature {
	return &RuleSignature{fmt.Sprintf("r%d", id), ante, cons}
}

func (rs *RuleSignature) RuleString() string {
	s := ""
	for _, t := range rs.Ante {
		s += t.String() + " "
	}
	s += "->"
	for _, t := range rs.Cons {
		s += " " + t.String()
	}
	return s
}

func (rs *RuleSignature) String() string {
	return rs.RuleId + ": " + rs.RuleString()
}

type ProofGraph struct {
	Atoms        *AtomSet
	Observations []*Term
	Assumptions  []*Term
	RuleSigs     []*RuleSignature
}

func NewProofGraph() *ProofGraph {
	return &ProofGraph{Atoms: NewAtomSet()}
}

func (pg *ProofGraph) AddObservation(t *Term) {
	pg.Atoms.Add(t, 0)
	pg.Observations = append(pg.Observations, t)
}

func (pg *ProofGraph) AddAssumption(t *Term) {
	pg.Atoms.Add(t, 0)
	pg.Assumptions = append(pg.Assumptions, t)
}

var varUid int

func (pg *ProofGraph) Close(rules []*Rule) {
	level, maxRuleId := 0, 0
	augmented := true
	for augmented {
		//fmt.Println("# closing atom set - level", level)
		augmented = false
		for _, r := range rules {
			vars := make(map[string]string)
			r.Backchain(pg.Atoms, vars, level, func() {
				var uidVars []string
				ids := make(map[string]string)
				for _, t := range r.Ante {
					for _, a := range t.Args {
						if a[0] == '$' {
							comps := strings.Split(a, "#")
							if len(comps) == 2 {
								v := comps[0]
								c := comps[1]
								id, ok := ids[c]
								if !ok {
									varUid++
									id = fmt.Sprintf("%d", varUid)
									ids[c] = id
								}
								vars[a] = (v + id)[1:]
								uidVars = append(uidVars, a)
							}
						}
					}
				}
				var ante []*Term
				for _, a := range r.Ante {
					a2, g := a.Subst(vars)
					if !g {
						panic(fmt.Sprintf("atom isn't ground: %s (%s)", r, a))
					}
					pg.Atoms.Add(a2, level+1)
					ante = append(ante, a2)
				}
				var cons []*RuleConsTerm
				for _, a := range r.Cons {
					a2, _ := a.Term.Subst(vars)
					cons = append(cons, &RuleConsTerm{a2, a.Exclusive})
				}
				maxRuleId++
				sig := NewRuleSignature(maxRuleId, ante, cons)
				augmented = true
				pg.RuleSigs = append(pg.RuleSigs, sig)
				for _, v := range uidVars {
					delete(vars, v)
				}
			})
		}
		level++
	}
}

type Mapping struct {
	strNum map[string]int
	numStr map[int]string
	maxId  int
}

func NewMapping() *Mapping {
	strNum := make(map[string]int)
	numStr := make(map[int]string)
	return &Mapping{strNum, numStr, 0}
}

func (m *Mapping) Add(atom string) {
	if _, ok := m.strNum[atom]; !ok {
		m.maxId++
		m.strNum[atom] = m.maxId
		m.numStr[m.maxId] = atom
	}
}

type Theory struct {
	Clauses [][]string
}

func (th *Theory) Require(t *Term) {
	th.Clauses = append(th.Clauses, []string{t.String()})
}

func (th *Theory) String() string {
	s := ""
	for _, c := range th.Clauses {
		s += strings.Join(c, " ∨ ") + "\n"
	}
	return s
}

func (pg *ProofGraph) IsObservation(t *Term) bool {
	for _, o := range pg.Observations {
		if o.String() == t.String() {
			return true
		}
	}
	return false
}

func (pg *ProofGraph) IsAssumption(t *Term) bool {
	for _, o := range pg.Assumptions {
		if o.String() == t.String() {
			return true
		}
	}
	return false
}

func (pg *ProofGraph) Theory() *Theory {
	var clauses [][]string
	for _, a := range pg.Observations {
		clauses = append(clauses, []string{a.String()})
	}
	for _, sig := range pg.RuleSigs {
		for _, a := range sig.Ante {
			clause := []string{"-@" + sig.RuleId}
			clause = append(clause, a.String())
			clauses = append(clauses, clause)
		}
		for _, a := range sig.Cons {
			clause := []string{"-@" + sig.RuleId}
			clause = append(clause, a.String())
			clauses = append(clauses, clause)
		}
		for _, a := range sig.Cons {
			clause := []string{"-@" + sig.RuleId}
			clause = append(clause, "#"+a.String())
			clauses = append(clauses, clause)
		}
	}
	for _, tl := range pg.Atoms.Atoms {
		a := tl.Term
		var posRules, negRules []string
		for _, sig := range pg.RuleSigs {
			for _, a2 := range sig.Cons {
				if a.String() == a2.String() {
					posRules = append(posRules, "@"+sig.RuleId)
					if a2.Exclusive {
						negRules = append(negRules, "-@"+sig.RuleId)
					}
				}
			}
		}
		clause := []string{"-#" + a.String()}
		clause = append(clause, posRules...)
		clauses = append(clauses, clause)
		for i := 0; i < len(negRules); i++ {
			r1 := negRules[i]
			for j := i + 1; j < len(negRules); j++ {
				r2 := negRules[j]
				clauses = append(clauses, []string{r1, r2})
			}
		}
		if !pg.IsObservation(a) {
			var rules []string
			for _, sig := range pg.RuleSigs {
				for _, a2 := range sig.Ante {
					if a.String() == a2.String() {
						rules = append(rules, "@"+sig.RuleId)
					}
				}
			}
			clause := []string{"-" + a.String()}
			clause = append(clause, rules...)
			clauses = append(clauses, clause)
		}
		if pg.IsAssumption(a) {
			clause := []string{a.String()}
			clauses = append(clauses, clause)
		}
	}
	return &Theory{clauses}
}

// func (th *Theory) AllLiterals() []string {
// 	var lits []string
// 	for _, c := range th.Clauses {
// 		for _, l := range c {
// 			lits = append(lits, l)
// 		}
// 	}
// 	return lits
// }

func (th *Theory) Solve(cb func([]string)) {
	m := NewMapping()
	for _, c := range th.Clauses {
		for _, a := range c {
			if a[0] == '-' {
				a = a[1:]
			}
			m.Add(a)
		}
	}
	fmt.Println("#", len(th.Clauses), "clauses,", len(m.strNum), "literals")
	var clauses [][]int
	for _, c := range th.Clauses {
		var clause []int
		for _, a := range c {
			neg := a[0] == '-'
			if neg {
				a = a[1:]
			}
			lit := m.strNum[a]
			if neg {
				lit = -lit
			}
			clause = append(clause, lit)
		}
		clauses = append(clauses, clause)
	}
	sat.SolveAll(clauses, func(val map[int]bool) {
		var lits []string
		for a, b := range val {
			if b {
				lit := m.numStr[a+1]
				if lit[0] == '@' || lit[0] == '#' {
					// process applied/explained rules
				} else {
					lits = append(lits, lit)
				}
			}
		}
		sort.Slice(lits, func(i, j int) bool { return lits[i] < lits[j] })
		cb(lits)
	})
}
