#include "../bisim.sig".

#type agent_A tm.
#type agent_B tm.
#type agent_S tm.
#type minusone tm.

#type agent_A_def ((tm -> tm -> tm -> tm -> tm -> proc) -> o).
#type agent_B_def ((tm -> tm -> tm -> tm -> proc) -> o).
#type agent_S_def ((tm -> tm -> tm -> tm -> tm -> proc) -> o).
#type agent_System_def ((tm -> tm -> tm -> tm -> proc) -> o).

#type agent_ASpec_def ((tm -> tm -> tm -> tm -> tm -> tm -> proc) -> o).
#type agent_BSpec_def ((tm -> tm -> tm -> tm -> tm -> proc) -> o).
#type agent_SSpec_def ((tm -> tm -> tm -> tm -> tm -> tm -> proc) -> o).
#type agent_SystemSpec_def ((tm -> tm -> tm -> tm -> proc) -> o).

#type check_bisim o.
