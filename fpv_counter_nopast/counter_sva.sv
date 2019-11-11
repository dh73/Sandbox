`default_nettype none
module counter_sva #(parameter N=8)
   (input  wire          i_clk, i_rstn,
    input  wire 	 i_en,
    input  wire 	 i_load,
    input  wire 	 i_dir,
    input  wire  [N-1:0] i_data,
    input  wire  [N-1:0] o_result,
    input  wire          o_full,
    input  wire          o_empty);

   // Default clock and reset configs
   default clocking fpv_clk @(posedge i_clk); endclocking
   default disable iff (!i_rstn);

   // Sequences
   /* The o_done output is asserted when counter is full.
      This sequence is to avoid large and fixed times to define
      a property for o_done. Also, to disable i_en so I can
      mantain old counter value in next clock tick. */
   sequence wait_for_full_asserted;
      (i_en && i_dir && !o_full)[*] ##1 (o_full && !i_en);
   endsequence // wait_for_full_asserted

   sequence wait_for_empty_asserted;
      (i_en &&!i_dir && !o_empty)[*] ##1 (o_empty && !i_en);
   endsequence // wait_for_empty_asserted
   
   // Properties
   /* The counter underflows if o_result is 0                                                                                                        
    and i_dir is 0 (decrement) */
   property underflow_counter;
      (i_en && !i_load && !i_dir && o_result == {N{1'b0}} |-> ##1 o_result == {N{1'b1}});
   endproperty // underflow_counter
   a_underflow_counter: assert property (underflow_counter);
   
   /* The counter overflow if o_result is full 
      and i_dir is 1 (increment) */
   property overflow_counter;
      (i_en && !i_load && i_dir && o_result == {N{1'b1}} |-> ##1 o_result == {N{1'b0}});
   endproperty // overflow_counter
   a_overflow_counter: assert property (overflow_counter);
   
   /* If i_load is asserted, the value must be reflected at o_result
      output in the next clock cycle. 
      Using a local variable (data_s) to avoid $past() system function. */
   property counter_load;
      logic [N-1:0] data_s;
       (i_en && i_load && !$stable(i_data), data_s=i_data)
       |-> ##1 o_result == data_s;
   endproperty // counter_load
   a_counter_load: assert property (counter_load);
   
   /* If i_en is deasserted, the counter is disabled */
   property counter_disabled;
      (!i_en |-> ##1 $stable(o_result));
   endproperty // counter_disabled
   a_counter_disabled: assert property (counter_disabled);
   
   /* Counter can reach its max value if i_en and i_dir are set.
      Since I cannot use s_eventually, and exact and large time delays
      are expensive in FPV, an infinite delay until o_results becomes full
      does the job */
   property counter_reach_max;
      (o_result == {N{1'b0}} and wait_for_full_asserted |-> ##1 o_result == {N{1'b1}});
   endproperty // counter_reach_max
   a_counter_reach_max: assert property (counter_reach_max);
   
   // Same as counter_reach_max, but decreasing value
   property counter_reach_min;
      (o_result == {N{1'b1}} and wait_for_empty_asserted |-> ##1 o_result == {N{1'b0}});
   endproperty // counter_reach_min
   a_counter_reach_min: assert property (counter_reach_min);

   /* A special note on properties counter_reach_max and counter reach min:
      We're not taking into account if i_load and i_data are asserted at any time,
      during this process. Therefore, a bounded check will fail for that specific case.
      We could modify the sequences wait_for_full_asserted and wait_for_empty_asserted,
      to deassert both i_load and i_data. Then, we could create two cover points to 
      cover the cases I've just mentioned. */
endmodule // counter
`default_nettype wire

// Connecting the DUV and checker
bind counter counter_sva fpv_test (.*);

