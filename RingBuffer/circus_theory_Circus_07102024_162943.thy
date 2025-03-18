theory circus_theory_Circus 
	imports Axiomatic_Circus
begin

subsection \<open> Prelude \<close>

lit_vars
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>

type_synonym Chem = nat
type_synonym Intensity = nat

	
	
datatype NIDS_GasAnalysis_stm_Chemical = 
	NID_i1_GasAnalysis_stm_Chemical | 
	NID_GasDetected_GasAnalysis_stm_Chemical | 
	NID_j1_GasAnalysis_stm_Chemical | 
	NID_Reading_GasAnalysis_stm_Chemical | 
	NID_Analysis_GasAnalysis_stm_Chemical | 
	NID_NoGas_GasAnalysis_stm_Chemical	
	
datatype Status = 
	noGas | 
	gasD	
	
datatype Angle = 
	Left | 
	Right | 
	Back | 
	Front

record GasSensor =
	c :: "Chem"
	i :: "Intensity"


\<comment> \<open>constant and function declaration\<close>
consts intensity :: "(GasSensor list) \<Rightarrow> Intensity"

consts location :: "(GasSensor list) \<Rightarrow> Angle"

consts goreq :: "Intensity\<times>Intensity \<Rightarrow> boolean"

consts angle :: "nat \<Rightarrow> Angle"

consts analysis :: "(GasSensor list) \<Rightarrow> Status"


\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>internal_channel_GasAnalysis_stm_Chemical\<close>

internal__GasAnalysis_stm_Chemical :: "NIDS_GasAnalysis_stm_Chemical"
	
\<comment> \<open>flowchannel_GasAnalysis_stm_Chemical\<close>

interrupt_GasAnalysis_stm_Chemical :: unit 
exited_GasAnalysis_stm_Chemical :: unit 
exit_GasAnalysis_stm_Chemical :: unit 
terminate :: unit 
	
\<comment> \<open>variable_channel_GasAnalysis_stm_Chemical\<close>

get_sts :: "Status"
set_sts :: "Status"
setL_sts :: "Status"
setR_sts :: "Status"

get_gs :: "(GasSensor list)"
set_gs :: "(GasSensor list)"
setL_gs :: "(GasSensor list)"
setR_gs :: "(GasSensor list)"

get_ins :: "Intensity"
set_ins :: "Intensity"
setL_ins :: "Intensity"
setR_ins :: "Intensity"

get_anl :: "Angle"
set_anl :: "Angle"
setL_anl :: "Angle"
setR_anl :: "Angle"
	
\<comment> \<open>event_channel_GasAnalysis_stm_Chemical\<close>

gas_in :: "(GasSensor list)"
gas_out :: "(GasSensor list)"

resume_in :: unit 
resume_out :: unit 

turn_in :: "Angle"
turn_out :: "Angle"

stop_in :: unit 
stop_out :: unit 

gas__in :: "NIDS_GasAnalysis_stm_Chemical\<times>(GasSensor list)"

resume__in :: "NIDS_GasAnalysis_stm_Chemical"

turn__in :: "NIDS_GasAnalysis_stm_Chemical\<times>Angle"

stop__in :: "NIDS_GasAnalysis_stm_Chemical"
	
\<comment> \<open>junction_channel_i1_GasAnalysis_stm_Chemical\<close>

enter_i1_GasAnalysis_stm_Chemical :: unit 
interrupt_i1_GasAnalysis_stm_Chemical :: unit 
	
\<comment> \<open>state_channel_GasDetected_GasAnalysis_stm_Chemical\<close>

enter_GasDetected_GasAnalysis_stm_Chemical :: unit 
entered_GasDetected_GasAnalysis_stm_Chemical :: unit 
interrupt_GasDetected_GasAnalysis_stm_Chemical :: unit 
enteredL_GasDetected_GasAnalysis_stm_Chemical :: unit 
enteredR_GasDetected_GasAnalysis_stm_Chemical :: unit 
	
\<comment> \<open>state_channel_j1_GasAnalysis_stm_Chemical\<close>

enter_j1_GasAnalysis_stm_Chemical :: unit 
entered_j1_GasAnalysis_stm_Chemical :: unit 
interrupt_j1_GasAnalysis_stm_Chemical :: unit 
enteredL_j1_GasAnalysis_stm_Chemical :: unit 
enteredR_j1_GasAnalysis_stm_Chemical :: unit 
	
\<comment> \<open>state_channel_Reading_GasAnalysis_stm_Chemical\<close>

enter_Reading_GasAnalysis_stm_Chemical :: unit 
entered_Reading_GasAnalysis_stm_Chemical :: unit 
interrupt_Reading_GasAnalysis_stm_Chemical :: unit 
enteredL_Reading_GasAnalysis_stm_Chemical :: unit 
enteredR_Reading_GasAnalysis_stm_Chemical :: unit 
	
\<comment> \<open>state_channel_Analysis_GasAnalysis_stm_Chemical\<close>

enter_Analysis_GasAnalysis_stm_Chemical :: unit 
entered_Analysis_GasAnalysis_stm_Chemical :: unit 
interrupt_Analysis_GasAnalysis_stm_Chemical :: unit 
enteredL_Analysis_GasAnalysis_stm_Chemical :: unit 
enteredR_Analysis_GasAnalysis_stm_Chemical :: unit 
	
\<comment> \<open>state_channel_NoGas_GasAnalysis_stm_Chemical\<close>

enter_NoGas_GasAnalysis_stm_Chemical :: unit 
entered_NoGas_GasAnalysis_stm_Chemical :: unit 
interrupt_NoGas_GasAnalysis_stm_Chemical :: unit 
enteredL_NoGas_GasAnalysis_stm_Chemical :: unit 
enteredR_NoGas_GasAnalysis_stm_Chemical :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_GasAnalysis_stm_Chemical = \<lbrace> 
	  enter_i1_GasAnalysis_stm_Chemical, 
	  enter_GasDetected_GasAnalysis_stm_Chemical, 
	  enter_j1_GasAnalysis_stm_Chemical, 
	  enter_Reading_GasAnalysis_stm_Chemical, 
	  enter_Analysis_GasAnalysis_stm_Chemical, 
	  enter_NoGas_GasAnalysis_stm_Chemical \<rbrace>"
	
definition "enteredSS_GasAnalysis_stm_Chemical = \<lbrace> 
	  entered_NoGas_GasAnalysis_stm_Chemical, 
	  entered_GasDetected_GasAnalysis_stm_Chemical, 
	  entered_Reading_GasAnalysis_stm_Chemical, 
	  entered_Analysis_GasAnalysis_stm_Chemical, 
	  entered_j1_GasAnalysis_stm_Chemical \<rbrace>"
	
definition "internal_events_GasAnalysis_stm_Chemical = \<lbrace> 
	  enter_i1_GasAnalysis_stm_Chemical, 
	  enter_GasDetected_GasAnalysis_stm_Chemical, 
	  enter_j1_GasAnalysis_stm_Chemical, 
	  enter_Reading_GasAnalysis_stm_Chemical, 
	  enter_Analysis_GasAnalysis_stm_Chemical, 
	  enter_NoGas_GasAnalysis_stm_Chemical, 
	  entered_NoGas_GasAnalysis_stm_Chemical, 
	  entered_GasDetected_GasAnalysis_stm_Chemical, 
	  entered_Reading_GasAnalysis_stm_Chemical, 
	  entered_Analysis_GasAnalysis_stm_Chemical, 
	  entered_j1_GasAnalysis_stm_Chemical, 
	  interrupt_GasAnalysis_stm_Chemical, 
	  exited_GasAnalysis_stm_Chemical \<rbrace>"
	
definition "shared_variable_events_GasAnalysis_stm_Chemical = \<lbrace> 
 \<rbrace>"
	
definition "sem__events_GasAnalysis_stm_Chemical = \<lbrace> 
	  terminate, 
	  gas_in, 
	  gas_out, 
	  resume_in, 
	  resume_out, 
	  turn_in, 
	  turn_out, 
	  stop_in, 
	  stop_out \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
	"relu x = max 0 x"


locale stm_GasAnalysis_stm_Chemical
begin

actions  is "(mychan, unit) action" where 
"SSTOP = share  \<rightarrow>  SSTOP" |

"Inactive_i1_GasAnalysis_stm_Chemical = (SSTOP \<triangle> (Activation_i1_GasAnalysis_stm_Chemical
  \<box>
  Termination_i1_GasAnalysis_stm_Chemical))" | 

"Activation_i1_GasAnalysis_stm_Chemical = (enter_i1_GasAnalysis_stm_Chemical \<rightarrow> Active_i1_GasAnalysis_stm_Chemical)" | 

"Termination_i1_GasAnalysis_stm_Chemical = (terminate \<rightarrow> Skip)" | 

"Active_i1_GasAnalysis_stm_Chemical = ((SSTOP \<triangle> (interrupt_i1_GasAnalysis_stm_Chemical \<rightarrow> Skip));; Inactive_i1_GasAnalysis_stm_Chemical)" | 

"Inactive_GasDetected_GasAnalysis_stm_Chemical = (SSTOP \<triangle> (Activation_GasDetected_GasAnalysis_stm_Chemical
  \<box>
  Termination_GasDetected_GasAnalysis_stm_Chemical))" | 

"Activation_GasDetected_GasAnalysis_stm_Chemical = (enter_GasDetected_GasAnalysis_stm_Chemical \<rightarrow> Active_GasDetected_GasAnalysis_stm_Chemical)" | 

"Termination_GasDetected_GasAnalysis_stm_Chemical = (terminate \<rightarrow> Skip)" | 

"Active_GasDetected_GasAnalysis_stm_Chemical = ((SSTOP \<triangle> (get_gs?(gs) \<rightarrow> ((size(gs) > 0) & ((SSTOP \<triangle> (set_ins!intensity(gs) \<rightarrow> Skip))))));; (Behaviour_GasDetected_GasAnalysis_stm_Chemical;; Exiting_GasDetected_GasAnalysis_stm_Chemical))" | 

"Behaviour_GasDetected_GasAnalysis_stm_Chemical = (entered_GasDetected_GasAnalysis_stm_Chemical \<rightarrow> During_GasDetected_GasAnalysis_stm_Chemical)" | 

"During_GasDetected_GasAnalysis_stm_Chemical = ((Skip;; SSTOP) \<triangle> (interrupt_GasDetected_GasAnalysis_stm_Chemical \<rightarrow> Skip))" | 

"Exiting_GasDetected_GasAnalysis_stm_Chemical = ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip));; (Skip;; (exited_GasAnalysis_stm_Chemical \<rightarrow> Inactive_GasDetected_GasAnalysis_stm_Chemical)))" | 

"Inactive_j1_GasAnalysis_stm_Chemical = (SSTOP \<triangle> (Activation_j1_GasAnalysis_stm_Chemical
  \<box>
  Termination_j1_GasAnalysis_stm_Chemical))" | 

"Activation_j1_GasAnalysis_stm_Chemical = (enter_j1_GasAnalysis_stm_Chemical \<rightarrow> Entering_j1_GasAnalysis_stm_Chemical)" | 

"Termination_j1_GasAnalysis_stm_Chemical = (terminate \<rightarrow> Skip)" | 

"Entering_j1_GasAnalysis_stm_Chemical = (entered_j1_GasAnalysis_stm_Chemical \<rightarrow> Active_j1_GasAnalysis_stm_Chemical)" | 

"Active_j1_GasAnalysis_stm_Chemical = (SSTOP \<triangle> (Termination_j1_GasAnalysis_stm_Chemical
  \<box>
  (interrupt_j1_GasAnalysis_stm_Chemical \<rightarrow> Interrupted_j1_GasAnalysis_stm_Chemical)))" | 

"Interrupted_j1_GasAnalysis_stm_Chemical = (SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> (exited_GasAnalysis_stm_Chemical \<rightarrow> Inactive)))" | 

"Inactive_Reading_GasAnalysis_stm_Chemical = (SSTOP \<triangle> (Activation_Reading_GasAnalysis_stm_Chemical
  \<box>
  Termination_Reading_GasAnalysis_stm_Chemical))" | 

"Activation_Reading_GasAnalysis_stm_Chemical = (enter_Reading_GasAnalysis_stm_Chemical \<rightarrow> Active_Reading_GasAnalysis_stm_Chemical)" | 

"Termination_Reading_GasAnalysis_stm_Chemical = (terminate \<rightarrow> Skip)" | 

"Active_Reading_GasAnalysis_stm_Chemical = (Skip;; (Behaviour_Reading_GasAnalysis_stm_Chemical;; Exiting_Reading_GasAnalysis_stm_Chemical))" | 

"Behaviour_Reading_GasAnalysis_stm_Chemical = (entered_Reading_GasAnalysis_stm_Chemical \<rightarrow> During_Reading_GasAnalysis_stm_Chemical)" | 

"During_Reading_GasAnalysis_stm_Chemical = ((Skip;; SSTOP) \<triangle> (interrupt_Reading_GasAnalysis_stm_Chemical \<rightarrow> Skip))" | 

"Exiting_Reading_GasAnalysis_stm_Chemical = ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip));; (Skip;; (exited_GasAnalysis_stm_Chemical \<rightarrow> Inactive_Reading_GasAnalysis_stm_Chemical)))" | 

"Inactive_Analysis_GasAnalysis_stm_Chemical = (SSTOP \<triangle> (Activation_Analysis_GasAnalysis_stm_Chemical
  \<box>
  Termination_Analysis_GasAnalysis_stm_Chemical))" | 

"Activation_Analysis_GasAnalysis_stm_Chemical = (enter_Analysis_GasAnalysis_stm_Chemical \<rightarrow> Active_Analysis_GasAnalysis_stm_Chemical)" | 

"Termination_Analysis_GasAnalysis_stm_Chemical = (terminate \<rightarrow> Skip)" | 

"Active_Analysis_GasAnalysis_stm_Chemical = (Skip;; (Behaviour_Analysis_GasAnalysis_stm_Chemical;; Exiting_Analysis_GasAnalysis_stm_Chemical))" | 

"Behaviour_Analysis_GasAnalysis_stm_Chemical = (entered_Analysis_GasAnalysis_stm_Chemical \<rightarrow> During_Analysis_GasAnalysis_stm_Chemical)" | 

"During_Analysis_GasAnalysis_stm_Chemical = (((SSTOP \<triangle> (get_gs?(gs) \<rightarrow> ((size(gs) > 0) & ((SSTOP \<triangle> (set_sts!analysis(gs) \<rightarrow> Skip))))));; SSTOP) \<triangle> (interrupt_Analysis_GasAnalysis_stm_Chemical \<rightarrow> Skip))" | 

"Exiting_Analysis_GasAnalysis_stm_Chemical = ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip));; (Skip;; (exited_GasAnalysis_stm_Chemical \<rightarrow> Inactive_Analysis_GasAnalysis_stm_Chemical)))" | 

"Inactive_NoGas_GasAnalysis_stm_Chemical = (SSTOP \<triangle> (Activation_NoGas_GasAnalysis_stm_Chemical
  \<box>
  Termination_NoGas_GasAnalysis_stm_Chemical))" | 

"Activation_NoGas_GasAnalysis_stm_Chemical = (enter_NoGas_GasAnalysis_stm_Chemical \<rightarrow> Active_NoGas_GasAnalysis_stm_Chemical)" | 

"Termination_NoGas_GasAnalysis_stm_Chemical = (terminate \<rightarrow> Skip)" | 

"Active_NoGas_GasAnalysis_stm_Chemical = (Skip;; (Behaviour_NoGas_GasAnalysis_stm_Chemical;; Exiting_NoGas_GasAnalysis_stm_Chemical))" | 

"Behaviour_NoGas_GasAnalysis_stm_Chemical = (entered_NoGas_GasAnalysis_stm_Chemical \<rightarrow> During_NoGas_GasAnalysis_stm_Chemical)" | 

"During_NoGas_GasAnalysis_stm_Chemical = ((Skip;; SSTOP) \<triangle> (interrupt_NoGas_GasAnalysis_stm_Chemical \<rightarrow> Skip))" | 

"Exiting_NoGas_GasAnalysis_stm_Chemical = ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip));; (Skip;; (exited_GasAnalysis_stm_Chemical \<rightarrow> Inactive_NoGas_GasAnalysis_stm_Chemical)))" | 

"composeNodes = (((((Inactive_NoGas_GasAnalysis_stm_Chemical
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_GasDetected_GasAnalysis_stm_Chemical)
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_Reading_GasAnalysis_stm_Chemical)
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_Analysis_GasAnalysis_stm_Chemical)
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_i1_GasAnalysis_stm_Chemical)
  \<lbrakk> | \<lbrace> share,terminate \<rbrace> | \<rbrakk> 
  Inactive_j1_GasAnalysis_stm_Chemical)" | 

"Trans_GasAnalysis_stm_Chemical = (SSTOP \<triangle> (get_sts?(sts) \<rightarrow> (get_ins?(ins) \<rightarrow> (((((((((((internal__GasAnalysis_stm_Chemical.(NID_i1_GasAnalysis_stm_Chemical) \<rightarrow> ((SSTOP \<triangle> (set_gs![] \<rightarrow> Skip));; (SSTOP \<triangle> (set_anl!Front \<rightarrow> Skip))));; (enter_Reading_GasAnalysis_stm_Chemical \<rightarrow> Skip))
  \<box>
  ((gas__in.(NID_Reading_GasAnalysis_stm_Chemical)?(gs) \<rightarrow> (SSTOP \<triangle> (set_gs!gs \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_stm_Chemical \<rightarrow> Skip);; (enter_Analysis_GasAnalysis_stm_Chemical \<rightarrow> Skip))))))
  \<box>
  ((internal__GasAnalysis_stm_Chemical.(NID_NoGas_GasAnalysis_stm_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_stm_Chemical \<rightarrow> Skip);; (enter_Reading_GasAnalysis_stm_Chemical \<rightarrow> Skip))))))
  \<box>
  ((sts = noGas) & (((internal__GasAnalysis_stm_Chemical.(NID_Analysis_GasAnalysis_stm_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_stm_Chemical \<rightarrow> (SSTOP \<triangle> (resume_out \<rightarrow> Skip)));; (enter_NoGas_GasAnalysis_stm_Chemical \<rightarrow> Skip))))))))
  \<box>
  ((sts = gasD) & (((internal__GasAnalysis_stm_Chemical.(NID_Analysis_GasAnalysis_stm_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_stm_Chemical \<rightarrow> Skip);; (enter_GasDetected_GasAnalysis_stm_Chemical \<rightarrow> Skip))))))))
  \<box>
  (goreq(ins,thr) & (((internal__GasAnalysis_stm_Chemical.(NID_GasDetected_GasAnalysis_stm_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_stm_Chemical \<rightarrow> (SSTOP \<triangle> (stop_out \<rightarrow> Skip)));; (enter_j1_GasAnalysis_stm_Chemical \<rightarrow> Skip))))))))
  \<box>
  ((\<not>goreq(ins,thr)) & (((internal__GasAnalysis_stm_Chemical.(NID_GasDetected_GasAnalysis_stm_Chemical) \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_GasAnalysis_stm_Chemical \<rightarrow> ((SSTOP \<triangle> (get_gs?(gs) \<rightarrow> ((size(gs) > 0) & ((SSTOP \<triangle> (set_anl!location(gs) \<rightarrow> Skip))))));; (SSTOP \<triangle> (get_anl?(anl) \<rightarrow> (SSTOP \<triangle> (turn_out!anl \<rightarrow> Skip))))));; (enter_Reading_GasAnalysis_stm_Chemical \<rightarrow> Skip))))))))
  \<box>
  (share \<rightarrow> Skip));; Trans_GasAnalysis_stm_Chemical)
  \<box>
  (((interrupt_GasAnalysis_stm_Chemical \<rightarrow> (SSTOP \<triangle> (exit_GasAnalysis_stm_Chemical \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_GasAnalysis_stm_Chemical \<rightarrow> (terminate \<rightarrow> Skip))))
  \<box>
  (terminate \<rightarrow> Skip))))))" | 

"ncCoreBehaviour_GasAnalysis_stm_Chemical = ((((composeNodes [ interrupt_i1_GasAnalysis_stm_Chemical \<mapsto> internal__GasAnalysis_stm_Chemical\<cdot>NID_i1_GasAnalysis_stm_Chemical,  
 interrupt_Reading_GasAnalysis_stm_Chemical \<mapsto> gas__in\<cdot>NID_Reading_GasAnalysis_stm_Chemical,  
 interrupt_NoGas_GasAnalysis_stm_Chemical \<mapsto> internal__GasAnalysis_stm_Chemical\<cdot>NID_NoGas_GasAnalysis_stm_Chemical,  
 interrupt_Analysis_GasAnalysis_stm_Chemical \<mapsto> internal__GasAnalysis_stm_Chemical\<cdot>NID_Analysis_GasAnalysis_stm_Chemical,  
 interrupt_Analysis_GasAnalysis_stm_Chemical \<mapsto> internal__GasAnalysis_stm_Chemical\<cdot>NID_Analysis_GasAnalysis_stm_Chemical,  
 interrupt_GasDetected_GasAnalysis_stm_Chemical \<mapsto> internal__GasAnalysis_stm_Chemical\<cdot>NID_GasDetected_GasAnalysis_stm_Chemical,  
 interrupt_GasDetected_GasAnalysis_stm_Chemical \<mapsto> internal__GasAnalysis_stm_Chemical\<cdot>NID_GasDetected_GasAnalysis_stm_Chemical,  
 interrupt_NoGas_GasAnalysis_stm_Chemical \<mapsto> interrupt_GasAnalysis_stm_Chemical,  
 interrupt_GasDetected_GasAnalysis_stm_Chemical \<mapsto> interrupt_GasAnalysis_stm_Chemical,  
 interrupt_Reading_GasAnalysis_stm_Chemical \<mapsto> interrupt_GasAnalysis_stm_Chemical,  
 interrupt_Analysis_GasAnalysis_stm_Chemical \<mapsto> interrupt_GasAnalysis_stm_Chemical,  
 interrupt_j1_GasAnalysis_stm_Chemical \<mapsto> interrupt_GasAnalysis_stm_Chemical ]) [ share \<mapsto> share,  
 set_sts \<mapsto> setL_sts,  
 set_ins \<mapsto> setL_ins ])
  \<lbrakk> | \<lbrace> enter_j1_GasAnalysis_stm_Chemical,internal__GasAnalysis_stm_Chemical\<cdot>NID_i1_GasAnalysis_stm_Chemical,enter_GasDetected_GasAnalysis_stm_Chemical,enter_Analysis_GasAnalysis_stm_Chemical,exit_GasAnalysis_stm_Chemical,internal__GasAnalysis_stm_Chemical\<cdot>NID_NoGas_GasAnalysis_stm_Chemical,gas__in\<cdot>NID_Reading_GasAnalysis_stm_Chemical,enter_i1_GasAnalysis_stm_Chemical,exited_GasAnalysis_stm_Chemical,setL_ins,internal__GasAnalysis_stm_Chemical\<cdot>NID_Analysis_GasAnalysis_stm_Chemical,interrupt_GasAnalysis_stm_Chemical,enter_Reading_GasAnalysis_stm_Chemical,setL_sts,internal__GasAnalysis_stm_Chemical\<cdot>NID_GasDetected_GasAnalysis_stm_Chemical,share,terminate,enter_NoGas_GasAnalysis_stm_Chemical \<rbrace> | \<rbrakk> 
  ((enter_i1_GasAnalysis_stm_Chemical \<rightarrow> Trans_GasAnalysis_stm_Chemical) [ share \<mapsto> share,  
 share \<mapsto> setL_sts,  
 share \<mapsto> setL_ins ])) [ setL_sts \<mapsto> set_sts,  
 setL_ins \<mapsto> set_ins ])" | 

"ncBehaviour_GasAnalysis_stm_Chemical = ((ncCoreBehaviour_GasAnalysis_stm_Chemical \<Zhide> \<lbrace> enter_i1_GasAnalysis_stm_Chemical,enter_GasDetected_GasAnalysis_stm_Chemical,enter_j1_GasAnalysis_stm_Chemical,enter_Reading_GasAnalysis_stm_Chemical,enter_Analysis_GasAnalysis_stm_Chemical,enter_NoGas_GasAnalysis_stm_Chemical,exit_GasAnalysis_stm_Chemical,exited_GasAnalysis_stm_Chemical,internal__GasAnalysis_stm_Chemical \<rbrace>) [ gas__in\<cdot>x \<mapsto> gas_in ])" | 

"machineBody_GasAnalysis_stm_Chemical = ((ncBehaviour_GasAnalysis_stm_Chemical
  \<lbrakk> | \<lbrace> interrupt_GasAnalysis_stm_Chemical \<rbrace> | \<rbrakk> 
  Skip) \<Zhide> \<lbrace> enteredSS_GasAnalysis_stm_Chemical \<rbrace>)" | 

"Memory_anl(value :: Angle) = (((get_anl!value \<rightarrow> Memory_anl(value))
  \<box>
  ((set_anl?(x__) \<rightarrow> Memory_anl(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"Memory_sts(value :: Status) = (((get_sts!value \<rightarrow> Memory_sts(value))
  \<box>
  ((set_sts?(x__) \<rightarrow> Memory_sts(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"Memory_ins(value :: Intensity) = (((get_ins!value \<rightarrow> Memory_ins(value))
  \<box>
  ((set_ins?(x__) \<rightarrow> Memory_ins(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"Memory_gs(value :: (GasSensor list)) = (((get_gs!value \<rightarrow> Memory_gs(value))
  \<box>
  ((set_gs?(x__) \<rightarrow> Memory_gs(x__))
  \<box>
  (terminate \<rightarrow> Skip))))" | 

"varMemory_GasAnalysis_stm_Chemical = (((Memory_anl(Front)
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  Memory_sts(noGas))
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  Memory_ins(0))
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  Memory_gs([]))" | 

"stateful_GasAnalysis_stm_Chemical = ((machineBody_GasAnalysis_stm_Chemical
  \<lbrakk> | \<lbrace> set_sts,get_sts,set_ins,set_anl,set_gs,terminate,get_anl,get_gs,get_ins \<rbrace> | \<rbrakk> 
  varMemory_GasAnalysis_stm_Chemical) \<Zhide> \<lbrace> set_sts,get_sts,set_ins,set_anl,set_gs,terminate,get_anl,get_gs,get_ins \<rbrace>)" | 

"sharedVarMemory_GasAnalysis_stm_Chemical = (terminate \<rightarrow> Skip)" | 

"stm_GasAnalysis_stm_Chemical = ((((((stateful_GasAnalysis_stm_Chemical \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip))) [  ])
  \<lbrakk> | \<lbrace> shared \<rbrace> | \<rbrakk> 
  Skip)
  \<lbrakk> | \<lbrace> terminate \<rbrace> | \<rbrakk> 
  sharedVarMemory_GasAnalysis_stm_Chemical) \<Zhide> \<lbrace>  \<rbrace>)"

\<comment> \<open>Main action of the process\<close>
definition "ProcDef = cProcess stm_mainaction_GasAnalysis_stm_Chemical"

end
 
end





