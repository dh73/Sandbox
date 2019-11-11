`default_nettype none
module counter #(parameter N=8)
   (input  wire          i_clk, i_rstn,
    input  wire 	 i_en,
    input  wire 	 i_load,
    input  wire 	 i_dir,
    input  wire  [N-1:0] i_data,
    output logic [N-1:0] o_result,
    output logic 	 o_full,
    output logic         o_empty);
    
   var logic [N-1:0] 	 ps;
   logic [N-1:0] 	 ns;

   always_ff @(posedge i_clk) begin
      if (~i_rstn)
	ps <= {N{1'b0}};
      else
	// Enable has priority over load
	if (i_en) begin
	   if (i_load)
	     ps <= i_data;
	   else
	     ps <= ns;
	end
   end // always_ff @ (posedge i_clk)

   assign ns = (i_dir) ? ps + 1'b1 : ps - 1'b1;
   assign o_full = (ps == {N{1'b1}});
   assign o_empty = (ps == {N{1'b0}});
   assign o_result = ps;
endmodule // counter
`default_nettype wire
