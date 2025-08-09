# dicer: probability distributions from dice notation

dicer is a library for computing probability distributions from [dice notation].

Specifically, it's designed distributions from [Dungeons and Dragons][D&D], 5th edition.
The dice expressions should support all rolls that one can make during play
(let [me] know about any gaps).

## Notation guide

dicer uses a [dice notation] that should be familiar to players of D&D.

Each _dice expression_ generates a _probability distribution_ of
integers. It's dicer's job to go from the expression to the distribution.

Here's the expressions dicer understands. We'll start simply and work up.

## Die, constant, addition

The two most basic expressions are _die_ expressions and _constant_ expressions.

Die expressions written `dN`, where `N` is a positive integer.
These generate a [discrete uniform distribution] between `1` and `N`, inclusive-- 
just like rolling a fair `N`-sided die.

Constant expressions are "just" integers, like `1` and `156417856`.
Constants generate single-value distributions: that integer, with probability 100%.

Expressions can be added with `+`. The resulting distribution is what you'd get from
rolling those values and performing the addition:

- `1 + 1` generates the single-value distribution `2`.
- `d10 + 10` generates a discrete uniform distribution between `11` and `20`, inclusive;
  rolling a 10-sided die (`1..=10`) and adding `10` to the result.
- `d2 + d2` generates a non-uniform distribution:

  | Value | Probability | Rolls |
  | ----- | ----------- | ---- |
  | 2     | 25% | 1 + 1
  | 3     | 50% | 1 + 2 or 2 + 1 |
  | 4     | 25% | 2 + 2 |


## Die repetition and keep-highest

Often, [D&D] will ask you to roll more than one of the same die.
For instance, 5th-level caster who hits with _firebolt_ will roll
two ten-sided dice for damage. dicer follows the standard notation for this,
`2d10`.

In some cases, the game requires rolling multiple dice but only keeping some results.
[Advantage][adv-dis] requires rolling two `d20`s and keeping the highest; [disadvantage][adv-dis],
keeping the lowest. A repeated expression can have the suffix `kh` (keep-highest) or `kl` (keep-lowest)
to reflect this: `2d20kh` represents a roll with advantage, `2d20kl` a roll with disadvantage.

The "keep" suffix can also have a number of rolls to keep.
When [rolling for ability scores](https://www.dndbeyond.com/sources/dnd/basic-rules-2014/step-by-step-characters#3DetermineAbilityScores),
a player rolls `4d6`, keeps the highest three rolls, and sums them;
dicer recognizes `4d6kh3` for this roll.

## Signs, arithemtic, and parentheses

A minus sign (`-`) in front of an expression negates it. `-d10` generates a uniform distribution `-1` to `-10` inclusive.
Constants can optionally have a `+` sign in front to make their sign explicit; `+5` and `5` are equivalent.

Subtraction works in the same way as addition: `1 - 1` generates a single-value distribution, `0`.
Note, however, that `d10 - d10` does not result in `0`: it results in a non-uniform distribution, from `-9` to `+9`.

Multiplication (`*` or `×`) of expressions is allowed, and follows the standard
[order of operations](https://en.wikipedia.org/wiki/Order_of_operations).
Note that multiplication is a distinct operation from repetition:
`2 × d10` means "roll a ten-sided die once, and multiply the result by two", while `2d10` means "roll two ten-sided dice and sum the results."
The distribution of `2 × d10` has a 0% probability of producing `3`.

Division (`/`) operates as integer (truncating) division, i.e. it rounds towards zero.
Note that division by zero is prohibited: `10 / (d10 - 1)` will generate an error, because the denominator

As we just saw, parentheses can be used to influence (override) order of operations.
As in math class, `2 × (1+1)` is `4`, and `2 × 1 + 1` is `3`.

## Comparison

Here's where things get complicated!

dicer supports _comparison expressions_ such as `d10 > 5`.

More generally, comparison expressions are of the form `A op B`,
where `A` and `B` are expressions and `op` is an operator:

| Meaning | Operator |
| ------ | ----- |
| Greater than | `>` |
| Greater than or equal to | `>=` or `≥` |
| Equal to | `=` or `==` |
| Less than or equal to | `<=` or `≤` |
| Less than | `<` |

Comparison expressions have only two values in their distribution: `0` or `1`.
The probability of `0` is the probability that the comparison will be _false_,
and the probability of `1` is the probability that the comparison will be _true_.

For example: `d10 > 5` generates:

| Value | Probability | True for `d10` rolling... |
| ----- | ------- | ---- |
| 0 | 50% | 1, 2, 3, 4, 5 |
| 1 | 50% | 6, 7, 8, 9, 10 |

More-complicated expressions are possible.
For instance, a skill contest might result in an expression like `d20 + 5 >= d20 + 3`,
where `+5` and `+3` are the character's modifiers.

Comparison expressions come up when computing damage probabilities. Consider:

> T'paa attacks the kobold with a dagger. T'paa's Dexterity is 13 (+1 modifier) and his level is 5 (proficiency bonus +3), so he attacks with a +4 modifier.
> The kobold's AC is 12. If T'paa hits, he will deal 1d4 + 1 piercing damage.
>
> How much damage will T'paa do to the kobold?

If we ignore critical hits and misses, we can express the likely _damage_ as:

```ignore
(1d20 + 4 >= 12) * (1d4 + 1)
```

If the attack misses, the comparison expression will have value `0`. If it hits, the whole expression will have the value of the `1d4 + 1` roll.

## Bindings

Sometimes, the same value of a roll must be used multiple times in the same expression.
In the above example, we ignored critical hits, because they require multiple comparisons against the attack roll (`d20`):

- Is the attack roll a 20? (Critical hit)
- Is the attack roll a 1? (Critical miss)
- Is the attack roll, plus modifiers, greater than or equal to the target AC? (Hit)
- Is the attack roll, plus modifiers, less than the target AC? (Miss)

To accomplish this, dicer allows _bindings_: assigning a name to an expression, then using the _same result_ for that expression in multiple places.
The binding syntax is `[NAME: roll] remainder`, where `NAME` is the name to assign, `roll` is the expression to give that name to, and `remainder`
is the expression to use the name in. In `remainder`, `NAME` stands in as the result of that roll.

For example, we can rewrite T'paa's attack roll as:

```ignore
[ATK: 1d20] (ATK + 4 >= 12) * (1d4 + 1)
```

We can then add the critical-miss case:

```ignore
[ATK: 1d20] (ATK > 1) * (ATK + 4 >= 12) * (1d4 + 1)
```

In this case, if the attack roll is 0, the whole expression will cancel out to zero - a miss.
But the same attack roll will be used for the comparison with AC (`12`).

Note how this is different from the (**incorrect**) expression:

```ignore
(1d20 > 1) * (1d20 + 4 >= 12) * (1d4 + 1)
```

which treats the "critical miss" and "to-hit" expressions as independent rolls.

We can further add [critical hits], where we roll an extra damage die on a 20:

```ignore
[ATK: 1d20] (ATK = 20) * (2d4 + 1) + (ATK < 20) * (ATK > 1) * (ATK + 4 >= 12) * (1d4 + 1)
```

It's also possible to use more than one binding, which we'll see in a moment.

## Generalized repetition

Phew. One last thing to cover: generalized repetition.

Above, we talked about repetition as repeatedly rolling a die. 
It's actually more general: _any expression_ can be repeated.

For instance, consider a fighter with multiattack.
When they take the attack action, they make the attack roll multiple times.
What would be the expected value of damage in such a case?

We can repeat the whole attack roll by enclosing it in parentheses, and concatenating it with another expression (like `2`):

```ignore
2([ATK: 1d20] (ATK = 20) * (2d4 + 1) + (ATK < 20) * (ATK > 1) * (ATK + 4 >= 12) * (1d4 + 1))
```

Some caveats:
- Constants as the "repeating factor", and dice as the "repeated factor", don't require parentheses.
  Other expressions do. That is, `2d10` is fine, but `(d2)d10` and `(d2)(2d20 + 1)`.
- If using a keep expression (`kl` or `kh`), the first factor must be at least the "keep" number.
  `(d3)d10kh2` will fail to produce a distribution, because the `d3` may only result in one roll, and we have to keep `2`.

## Space, and a final example

dicer ignores space, tabs, and newlines. That allows us to write a more complicated expression:

> T'paa is frustrated with this kobold, and lashes out [with _eldritch blast_].
>
> T'paa has a Charisma modifier of +5.
> As a level 5 character, he has a proficiency bonus of +3, and he casts two beams of _eldritch blast_;
> each beam hits or misses independently.
> With the Agonizing Blast feat, T'paa adds his Charisma modifier to the damage of each beam.
>
> T'paa is still close to the kobold after attacking with his dagger, so he has disadvantage on the attack.
> The kobold has an AC of 12. How much damage does T'paa do?


```ignore
[MOD: +5] [PROFICIENCY: +3] [AC: 12]
2 (
     [ATK: 2d20kl] [DIE: 1d10] [CRIT: 1d10] 
     (ATK = 20) * (DIE + CRIT + MOD) +
     (ATK < 20) * (ATK > 1) (ATK + MOD + PROFICIENCY >= AC) * (DIE + MOD)
)
```

[with _eldritch blast_]: https://cceckman.com/writing/eldritch-blast/
[critical hit]: https://www.dndbeyond.com/sources/dnd/basic-rules-2014/combat#CriticalHits
[discrete uniform distribution]: https://en.wikipedia.org/wiki/Discrete_uniform_distribution
[dice notation]: https://en.wikipedia.org/wiki/Dice_notation
[D&D]: https://en.wikipedia.org/wiki/Dungeons_%26_Dragons
[me]: https://cceckman.com
[adv-dis]: https://www.dndbeyond.com/sources/dnd/basic-rules-2014/using-ability-scores#AdvantageandDisadvantage
