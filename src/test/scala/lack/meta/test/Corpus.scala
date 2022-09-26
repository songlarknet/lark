package lack.meta.test

import lack.meta.test.hedgehog._

object Corpus:
  val colours: Gen[String] = Gen.elementIndexed(IndexedSeq(
    "rainbow",
    "variegated",
    "rufous",
    "yellow",
    "azure",
    "crimson",
    "red",
    "pink",
    "straw",
    "chestnut",
    "brown",
    "grey",
    "pied",
    "black",
    "sooty",
    "white",
    "golden"))

  val birds: Gen[String] = Gen.elementIndexed(IndexedSeq(
    "lorikeet",
    "cassowary",
    "emu",
    "ibis",
    "grebe",
    "koel",
    "frogmouth",
    "swamphen",
    "crake",
    "stone-curlew",
    "stilt",
    "avocet",
    "oystercatcher",
    "plover",
    "lapwing",
    "dotterel",
    "snipe",
    "jacana",
    "curlew",
    "sandpiper",
    "whimbrel",
    "godwit",
    "tern",
    "albatross",
    "petrel",
    "prion",
    "stork",
    "gannet",
    "cormorant",
    "darter",
    "bittern",
    "heron",
    "egret",
    "spoonbill",
    "osprey",
    "kite",
    "kingfisher",
    "kestrel",
    "cockatoo",
    "galah",
    "corella",
    "cockatiel",
    "parrot",
    "rosella",
    "pitta",
    "catbird",
    "fairywren",
    "spinebill",
    "honeyeater",
    "pardalote",
    "scrubwren",
    "thornbill",
    "gerygone",
    "babbler",
    "drongo",
    "whistler",
    "cuckooshrike",
    "triller",
    "sitella",
    "whipbird",
    "wedgebill",
    "currawong",
    "butcherbird",
    "magpie",
    "fantail",
    "riflebird",
    "monarch",
    "flycatcher",
    "robin",
    "finch",
    "wagtail"))
