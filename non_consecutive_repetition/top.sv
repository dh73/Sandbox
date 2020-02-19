`default_nettype none
`ifndef _TEST_
 `define _TEST_
package test;
   typedef enum logic [1:0] {idle, a, b, c} states_t;
endpackage // test
   
   import test::*;

`endif
   
   /* Dummy pattern generator, as follows:
    /`````\/`````\/`````\/`````\/`````\/`````\
    x  A  xx  B  xx  B  xx  B  xx  A  xx  C  x
    \.,.../\.,.../\.,.../\.,.../\.,.../\.,.../
    
    The assertions match two non-consecutive 'A' followed by
    one C */
   
module top
  (input wire i_clk, i_rstn, i_req,
   output logic o_running,
   output 	states_t o_sequence);
   
   states_t ps, ns;
   logic [0:0] 	count_ps, count_ns; 
   logic [1:0] 	countb_ps, countb_ns;
   logic 	clear, en, visited_a_completed, visited_b_completed;
   
   assign visited_a_completed = (count_ps == 2'd1);
   assign visited_b_completed = (countb_ps == 2'd2);
   
   always_ff @(posedge i_clk) begin
      if (~i_rstn) begin 
	 ps <= idle;
	 count_ps <= 2'd0;
	 countb_ps <= 2'd0;
      end
      else begin         
	 ps <= ns;
	 count_ps <= count_ns;
	 countb_ps <= countb_ns;
      end
   end
   
   always_comb begin
      countb_ns = countb_ps;
      count_ns = count_ps;
      ns = ps;
      
      unique case (ps)
	idle: begin
	   if (i_req) ns = a;
	   else       ns = idle;
	end
	a: begin 
	   if (visited_a_completed) begin
	      ns = c;
	      count_ns = 2'b0;
	   end
	   else begin
	      count_ns = count_ps + 1'b1;
	      ns = b;
	   end
	end
	b: begin
	   if (visited_b_completed) begin
	      ns = a;
	      countb_ns = 2'b0;
	   end
	   else begin
	      countb_ns = countb_ps + 1'b1;
	      ns = b;
	   end
	end // case: b
	c: begin
	   ns = idle;
	end
	default: ns = idle;
      endcase // unique case (ps)
   end // always_comb
   
   always_ff @(posedge i_clk) begin
      o_running <= 1'b0;
      unique case (ps)
	idle: begin
	   o_sequence <= idle;
	end
	a: begin
	   o_sequence <= a;
	   o_running <= 1'b1;
	end
	b: begin
	   o_sequence <= b;
	   o_running <= 1'b1;
	end
	c: begin
	   o_sequence <= c;
	   o_running <= 1'b1;
	end
      endcase // unique case (ps)
   end // always_ff @ (posedge i_clk)

`ifdef PURE_SVA
   // ----------------------------- What normally works in JG, not sure if in VC ---------------------------
   default clocking cb @(posedge i_clk); endclocking
   default disable iff (~i_rstn);
   assume property (i_req == 1'b1);
   let a_seq = o_sequence == a;
   
   ap0_easy_and_fool: assert property ($rose(i_req) |-> ##2 o_sequence == a 
				       ##1 o_sequence == b [*3] 
				       ##1 o_sequence == a 
				       ##1 o_sequence == c);
   
   ap1_complex_and_notgood: assert property ($rose(i_req) |-> ##2 o_sequence == a [=2] 
					     within o_sequence == b [=3] 
					     ##1 o_sequence == c);
   
   ap2_conversion_verbose: assert property ($rose(i_req) |-> ##2 o_sequence != a [*0:$]
					    ##1 a_seq ##1 o_sequence != a [*0:$]
					    ##1 a_seq ##1 o_sequence != a [*0:$]
					    ##1 o_sequence == c);
   
   ap3_compact: assert property ($rose(i_req) |-> ##2 a_seq [=2] ##1 o_sequence == c);
   // -------------------------------------------------------------------------------------------------------
`endif //  `ifdef PURE_SVA
   
   
 /* Using FSM */
 // -------------------------------- Helper logic -----------------------------------
   logic [1:0] a_count = 0;
   logic       trigger_on_req = 0;
   // Assumptions
   assume property (i_req);
   
   always_ff @(posedge i_clk) begin
      if (~i_rstn) begin
	 a_count <= 0;
	 trigger_on_req <= 0;
      end
      else begin
	 if (a_count == 2'd2 && trigger_on_req || ps == idle) begin // clear after sequence match
	    a_count <= 2'b00;
	    trigger_on_req <= 1'b0;
	 end
	 else if (o_sequence == a && trigger_on_req)
	   a_count <= a_count + 1'b1;
	 else if (i_req)
	   trigger_on_req <= 1'b1;
      end // else: !if(~i_rstn)
   end // always_ff @ (posedge i_clk)
   
   default clocking cb @(posedge i_clk); endclocking
   default disable iff (!i_rstn);
   helper_NonConsecutive_a2: assert property ((a_count == 2'd2) |-> o_sequence == c);
 //--------------------------------------------------------------------------------------
endmodule // top

