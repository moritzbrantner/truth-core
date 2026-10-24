/-!
Source-derived readings of Alex O'Connor's formulations of the problem of evil
(media-span witnesses pinned to youtube-corpus transcript segments).

Vocabulary, all of it parameters rather than definitions:

* `Being` — the things quantified over.
* `God g`, `Good g`, `AllPowerful g`, `AllLoving g` — `g` is a god, is (morally)
  good, all-powerful, all-loving.
* `WantsToRemoveAllEvil g`, `CanRemoveAllEvil g` — `g` wants to remove, and is
  able to remove, all the evil in the world.
* `PermitsSuchSuffering g` — `g` permits the actual extent of suffering, human
  and animal.
* `Sentence`, `SaysSomethingBad φ`, `moralEvilPremise` — sentences, `φ` saying
  of something that it is bad, and the premise that there is man-made evil.
* `Evil x`, `CanEliminate g x` — there is evil in `x`; `g` is able to eliminate
  the evil in `x`.
-/

namespace TruthCore.English.OConnor

universe u

/-- The logical problem's key premise, which O'Connor reports from J. L. Mackie:
"if a good god existed he would want to remove all evil and would have the
power to do so", so that "the existence of evil in the world therefore shows
that a good god doesn't exist".

O'Connor states the problem in his own narration ("if an all-powerful god
exists who is capable of eliminating all the evil in the world then why doesn't
he") but attributes the conclusion to Mackie, and the video goes on to Stephen
Law's evil-god challenge rather than defending Mackie. The reading captures
only the conditional premise. The further step from wanting and being able to
remove all evil to there being no evil is left implicit in the source and is
not part of this reading.

Source: Alex O'Connor, "Could God Be Evil?" (Alex O'Connor, 2020-12-04),
00:18–00:47.
-/
def GoodGodWouldRemoveAllEvilReading {Being : Sort u}
    (God Good WantsToRemoveAllEvil CanRemoveAllEvil : Being → Prop) : Prop :=
  ∀ g, God g → Good g → WantsToRemoveAllEvil g ∧ CanRemoveAllEvil g

/-- The problem of evil's man-made-evil premise ascribes moral wrongness. When
"we talk about evil concerning the criticism of the supposedly all loving God",
O'Connor sorts it into natural evil (earthquakes) and "man-made evil which are
things like murder and rape"; of the second he asks "why things like stealing,
rape and murder are moral wrong[s]", and answers that "the morals of human
activity are entirely subjective".

`moralEvilPremise` is the critic's premise that there is man-made evil (that
there are murders and rapes, which are evil). The reading says that this
sentence says something is bad. It says nothing about natural evil, which
O'Connor treats separately ("the only reason that we perceive these things as
evil is because they're harmful to us").

Source: Alex O'Connor, "Frank Turek thinks that Evil proves God's existence"
(Alex O'Connor, 2016-08-23), 02:06–03:36.
-/
def ManMadeEvilPremiseSaysSomethingBadReading {Sentence : Sort u}
    (SaysSomethingBad : Sentence → Prop) (moralEvilPremise : Sentence) : Prop :=
  SaysSomethingBad moralEvilPremise

/-- An all-powerful god is capable of eliminating all the evil in the world
("if an all-powerful god exists who is capable of eliminating all the evil in
the world then why doesn't he").

Read as what all-powerfulness includes: for every evil, an all-powerful being
can eliminate it. It says nothing about wanting to. Both sides of the debate
grant it, so it serves as shared background for the internal form.

Source: Alex O'Connor, "Could God Be Evil?" (Alex O'Connor, 2020-12-04),
00:18–00:47.
-/
def AllPowerfulCanEliminateEvilReading {Being : Sort u}
    (AllPowerful Evil : Being → Prop) (CanEliminate : Being → Being → Prop) : Prop :=
  ∀ g x, AllPowerful g → Evil x → CanEliminate g x

/-- The suffering problem's key premise: an all-powerful god who truly loves us
would not permit suffering on the actual scale ("why would an all-powerful god
who truly loves us permit such suffering to overwhelm our living existence").

The source poses a rhetorical question after describing "the positively
colossal amount of suffering"; the reading takes the question as asserting
that such a god would not permit it. That is an interpretation: on a weaker
reading the question only asks for a reason. The amount of suffering is the
datum; whether its existence makes God improbable (the evidential form) is not
part of the reading.

Source: Alex O'Connor, "Christianity's Biggest Problem" (Alex O'Connor,
2021-03-08), 00:51–01:46.
-/
def LovingGodWouldNotPermitSuchSufferingReading {Being : Sort u}
    (God AllPowerful AllLoving PermitsSuchSuffering : Being → Prop) : Prop :=
  ∀ g, God g → AllPowerful g → AllLoving g → ¬ PermitsSuchSuffering g

end TruthCore.English.OConnor
