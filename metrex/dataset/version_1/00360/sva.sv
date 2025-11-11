// SVA checker for sameRecFN. Bind this to the DUT. Provide a free-running clk and active-high rst_n.
module sameRecFN_sva #(
  parameter int expWidth = 3,
  parameter int sigWidth = 3
)(
  input  logic                    clk,
  input  logic                    rst_n,
  input  logic [expWidth+sigWidth:0] a,
  input  logic [expWidth+sigWidth:0] b,
  input  logic                    out
);
  localparam int W   = expWidth + sigWidth + 1;
  localparam int MSB = expWidth + sigWidth;

  // Parameter guard (avoids negative slice (sigWidth-2):0)
  initial assert (sigWidth >= 2) else $fatal(1, "sameRecFN_sva: sigWidth must be >= 2");

  // Decode fields the same way as DUT
  wire [3:0] top4A = a[MSB -: 4];
  wire [3:0] top4B = b[MSB -: 4];

  // Golden expression (mirrors DUT intent)
  wire exp_out =
       ((top4A[2:0] == 3'b000) || (top4A[2:0] == 3'b111))
         ? ((top4A == top4B) && (a[(sigWidth-2):0] == b[(sigWidth-2):0]))
         : (top4A[2:0] == 3'b110)
             ? (top4A == top4B)
             : (a == b);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Core functional equivalence (mask X on inputs)
  assert property ( (!$isunknown({a,b})) |-> (out == exp_out) )
    else $error("sameRecFN: out != spec");

  // Out must not be X/Z when inputs are known
  assert property ( (!$isunknown({a,b})) |-> (!$isunknown(out)) )
    else $error("sameRecFN: out is X/Z for known inputs");

  // Branch coverage: hit each case and both outcomes
  cover property ( (top4A[2:0] inside {3'b000,3'b111}) && out );
  cover property ( (top4A[2:0] inside {3'b000,3'b111}) && !out );

  cover property ( (top4A[2:0] == 3'b110) && out );
  cover property ( (top4A[2:0] == 3'b110) && !out );

  cover property ( (!(top4A[2:0] inside {3'b000,3'b111,3'b110})) && out );
  cover property ( (!(top4A[2:0] inside {3'b000,3'b111,3'b110})) && !out );

endmodule

// Example bind (adjust clk/rst_n identifiers to your environment):
// bind sameRecFN sameRecFN_sva #(.expWidth(expWidth), .sigWidth(sigWidth))
//   sameRecFN_sva_i ( .clk(tb_clk), .rst_n(tb_rst_n), .a(a), .b(b), .out(out) );