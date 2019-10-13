`default_nettype none
module ram
  #(//Memory parameters
    parameter depth = 256,
    parameter aw    = $clog2(depth),
    parameter memfile = "lol.hex")
   (input wire 		i_wb_clk,
    input wire [aw-1:0] i_wb_adr,
    input wire [31:0] 	i_wb_dat,
    input wire [3:0] 	i_wb_sel,
    input wire 		i_wb_we,
    input wire 		i_wb_cyc,
    output reg [31:0] 	o_wb_rdt);
   
   wire [3:0] 		we = {4{i_wb_we & i_wb_cyc}} & i_wb_sel;
   wire [aw-3:0] 	addr = i_wb_adr[aw-1:2];
   reg [31:0] 		mem [0:depth/4-1] /* verilator public */;
   reg [31:0] 		memtmp [0:depth/4-1];

   integer 		idx;
   initial begin
      if(|memfile) begin
	 $display("Preloading %m from %s", memfile);
	 $readmemh(memfile, memtmp);
	 for(idx=0; idx < (depth/4-1); idx = idx + 1) begin
	    mem[idx][7:0  ] = memtmp[idx][7:0  ];
	    mem[idx][15:8 ] = memtmp[idx][15:8 ];
	    mem[idx][23:16] = memtmp[idx][23:16];
	    mem[idx][31:24] = memtmp[idx][31:24];
	    $display("%d:%h",idx,mem[idx]);
	 end
      end
   end
   
   always @(posedge i_wb_clk) begin
      if (we[0]) mem[addr][7:0]	  <= i_wb_dat[7:0];
      if (we[1]) mem[addr][15:8]  <= i_wb_dat[15:8];
      if (we[2]) mem[addr][23:16] <= i_wb_dat[23:16];
      if (we[3]) mem[addr][31:24] <= i_wb_dat[31:24];
      o_wb_rdt <= mem[addr];
   end   
endmodule
