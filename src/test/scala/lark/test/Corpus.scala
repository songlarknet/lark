package lark.test

import lark.test.hedgehog._

object Corpus:
  val colours: Gen[String] = Gen.elementIndexed(IndexedSeq(
    "azure",
    "black",
    "brown",
    "chestnut",
    "crimson",
    "golden",
    "grey",
    "pied",
    "pink",
    "rainbow",
    "red",
    "rufous",
    "sooty",
    "straw",
    "variegated",
    "white",
    "yellow"))

  val birds: Gen[String] = Gen.elementIndexed(IndexedSeq(
    "avocet",
    "babbler",
    "bittern",
    "butcherbird",
    "cassowary",
    "catbird",
    "cockatiel",
    "cockatoo",
    "corella",
    "cormorant",
    "crake",
    "cuckooshrike",
    "curlew",
    "currawong",
    "darter",
    "dotterel",
    "drongo",
    "egret",
    "emu",
    "fairywren",
    "fantail",
    "finch",
    "flycatcher",
    "frogmouth",
    "galah",
    "gannet",
    "gerygone",
    "godwit",
    "grebe",
    "heron",
    "honeyeater",
    "ibis",
    "jacana",
    "kestrel",
    "kingfisher",
    "kite",
    "koel",
    "lapwing",
    "lorikeet",
    "magpie",
    "monarch",
    "osprey",
    "oystercatcher",
    "pardalote",
    "parrot",
    "petrel",
    "pitta",
    "plover",
    "prion",
    "riflebird",
    "robin",
    "rosella",
    "sandpiper",
    "scrubwren",
    "sitella",
    "snipe",
    "spinebill",
    "spoonbill",
    "stilt",
    "stone-curlew",
    "stork",
    "swamphen",
    "tern",
    "thornbill",
    "triller",
    "wagtail",
    "wedgebill",
    "whimbrel",
    "whipbird",
    "whistler"))
