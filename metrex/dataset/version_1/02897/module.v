

module sequencer
  (
   input 		  clock,
   input 		  reset,
   output 		  fpc_read,
   input 		  fpc_valid,
   input [63:0] 	  fpc_data,
   input 		  tpc_ready,
   output 		  tpc_write,
   output [63:0] 	  tpc_data,
   output reg 		  rvalid = 0,
   output reg 		  wvalid = 0,
   output reg [ABITS-1:0] address = 0,
   output reg [DBITS-1:0] wdata = 0,
   input [DBITS-1:0] 	  rdata,
   input [SBITS-1:0] 	  status
   );

   parameter RPIPE = 2; parameter ABITS = 16; parameter DBITS = 64; parameter SBITS = 16; parameter CBITS = 24; reg [CBITS-1:0] 	  count = 32'hDEADBEEF;
   reg [1:0] 		  state = 0;
   reg 			  inc = 0;

   wire 		  rvalid_next = (state == 3) && tpc_ready;
   wire 		  wvalid_next = (state == 2) && fpc_read;

   assign fpc_read = fpc_valid && ((state == 0) || (state == 2));

   always @ (posedge clock)
     begin
	rvalid <= rvalid_next;
	wvalid <= wvalid_next;
	address <= (state == 0) ? fpc_data[ABITS-1:0] :
		   address + (inc && (rvalid || wvalid));
	wdata <= fpc_data[DBITS-1:0];
	inc <= (state == 0) ? fpc_data[61] : inc;
	case(state)
	  0: count <= fpc_data[CBITS+31:32];
	  1: count <= count - 1'b1;
	  2: count <= count - wvalid_next;
	  3: count <= count - rvalid_next;
	endcase
	if(reset)
	  state <= 2'd0;
	else
	  begin
	     case(state)
	       0: state <= fpc_read ? fpc_data[63:62] : 2'd0; default: state <= (count[CBITS-1:1] == 0) ? 2'd0 : state;
	     endcase
	  end
     end
   delay_n #(.N(RPIPE)) delay_tpc_write
     (.clock(clock), .in(rvalid), .out(tpc_write));
   assign tpc_data = rdata;

endmodule

module delay_n
  (
   input  clock,
   input  in,
   output out
   );

   parameter N = 2;

   reg [N-1:0] sreg = 0;

   assign out = sreg[N-1];

   always @ (posedge clock)
     sreg <= {sreg[N-2:0],in};

endmodule
