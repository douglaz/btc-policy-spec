import BtcPolicy.Exhibits.Fixtures
import BtcPolicy.Exhibits.ReleaseKernel
import BtcPolicy.Exhibits.TwoRun
import BtcPolicy.Exhibits.Registration
import BtcPolicy.Exhibits.Ingress
import BtcPolicy.Exhibits.Admission
import BtcPolicy.Exhibits.Feasibility
import BtcPolicy.Exhibits.EndToEnd
import BtcPolicy.Exhibits.Ladder
import BtcPolicy.Exhibits.RungIngress
import BtcPolicy.Exhibits.Lifecycle
/-! Historical defects as executable exhibits (`ADR-0023` decision 6): every theorem over the
`current` value of a guard parameter lives in the exhibit modules imported above, under
`BtcPolicy/Exhibits/`, so flipping `current` in the module that owns it goes red THERE and nowhere
else, which is what the CI controls assert; beside each, the same trace under the withdrawn value.
Two are not parameters and cannot be flipped: `F58`, whose refuted theorem has no parameter, and
`F65`, whose withdrawn reading was a lost field rather than a rule value, so its trap is the quorum
its exhibit computes. Each defect looked correct, was built or nearly built, and broke; it is
retained there so the trap cannot be re-laid without a red build. The exhibits were one file until
it took most of every control's build; split by topic, the build checks the modules in parallel,
and each keeps its declarations' names and statements. This file holds no declaration of its own. -/
