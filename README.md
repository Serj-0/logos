# Logos
## About
Logos is a command line tool to generate truth tables for premises in propositional logic.
## Installation
```
git clone https://github.com/Serj-0/logos.git
cd logos
sudo make install
```
## Usage
`logos [OPTIONS] [PREMISES]`

Connectives are formatted as follows
|Connective|Symbol|
|-|-|
|NOT|~ or !|
|OR|\||
|AND|&|
|IMPLICATION|->|
|EQUIVALENCE|<-> or =|

Although it's not conventionally grammatical, negation of a connective is allowed and produces the same result as negation of the whole premise [example](####negation-example)
## Examples

```
$ logos 'a->b'
a | b | a->b
1 | 1 | 1
1 | 0 | 0
0 | 1 | 1
0 | 0 | 1
```
```
$ logos -p -l 'a->(e->f)<->b|a'
p = a → (e → f) ⟷ b ⋃ a
a | e | f | b | p
1 | 1 | 1 | 1 | 1
1 | 1 | 1 | 0 | 1
1 | 1 | 0 | 1 | 0
1 | 1 | 0 | 0 | 0
1 | 0 | 1 | 1 | 1
1 | 0 | 1 | 0 | 1
1 | 0 | 0 | 1 | 1
1 | 0 | 0 | 0 | 1
0 | 1 | 1 | 1 | 1
0 | 1 | 1 | 0 | 0
0 | 1 | 0 | 1 | 1
0 | 1 | 0 | 0 | 0
0 | 0 | 1 | 1 | 1
0 | 0 | 1 | 0 | 0
0 | 0 | 0 | 1 | 1
0 | 0 | 0 | 0 | 0
```
```
$ logos 'a=b' 'a->c' 'b->c'
a | b | c | a=b | a->c | b->c
1 | 1 | 1 | 1 | 1 | 1
1 | 1 | 0 | 1 | 0 | 0
1 | 0 | 1 | 0 | 1 | 1
1 | 0 | 0 | 0 | 0 | 1
0 | 1 | 1 | 0 | 1 | 1
0 | 1 | 0 | 0 | 1 | 0
0 | 0 | 1 | 1 | 1 | 1
0 | 0 | 0 | 1 | 1 | 1

```
#### Negation example
```
$ logos 'a!&b=!(a&b)'
a | b | a!&b=!(a&b)
1 | 1 | 1
1 | 0 | 1
0 | 1 | 1
0 | 0 | 1
```
