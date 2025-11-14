// SVA checker for top_module
// Bind this file: bind top_module top_module_sva chk (.*);

module top_module_sva (
  input  logic        clk,
  input  logic [7:0]  in,
  input  logic [8:0]  out,
  input  logic [7:0]  data_in,
  input  logic        parity,
  input  logic [2:0]  position
);

  // Small init pipeline to avoid false trips on first cycles
  logic [1:0] init_sr;
  always_ff @(posedge clk) init_sr <= {init_sr[0], 1'b1};
  wire ok1 = init_sr[0];
  wire ok2 = init_sr[1];

  // Helper: set of inputs that the encoder explicitly handles
  function automatic bit valid_enc(input logic [7:0] v);
    return (v==8'h00 || v==8'h01 || v==8'h02 || v==8'h04 ||
            v==8'h08 || v==8'h10 || v==8'h20 || v==8'h40);
  endfunction

  // Pipeline/functional checks for internal stages
  assert property (@(posedge clk) disable iff (!ok1) data_in == $past(in));
  assert property (@(posedge clk) disable iff (!ok1) parity  == ~(^$past(data_in)));
  assert property (@(posedge clk) disable iff (!ok1) out[8]  == $past(parity));
  assert property (@(posedge clk) disable iff (!ok2) out[8]  == ~(^$past(in,2))); // end-to-end parity

  // Priority encoder mapping (combinational) and registration into out[7:5]
  assert property (@(posedge clk) disable iff (!ok1) out[7:5] == $past(position));

  assert property (@(posedge clk) (in==8'h00) |-> position==3'b000);
  assert property (@(posedge clk) (in==8'h01) |-> position==3'b001);
  assert property (@(posedge clk) (in==8'h02) |-> position==3'b010);
  assert property (@(posedge clk) (in==8'h04) |-> position==3'b011);
  assert property (@(posedge clk) (in==8'h08) |-> position==3'b100);
  assert property (@(posedge clk) (in==8'h10) |-> position==3'b101);
  assert property (@(posedge clk) (in==8'h20) |-> position==3'b110);
  assert property (@(posedge clk) (in==8'h40) |-> position==3'b111);

  // For any other input, position drives X, and that X is registered into out[7:5] next cycle
  assert property (@(posedge clk) !valid_enc(in) |-> $isunknown(position));
  assert property (@(posedge clk) disable iff (!ok2) !valid_enc($past(in)) |-> $isunknown(out[7:5]));

  // Low bits are always zero
  assert property (@(posedge clk) disable iff (!ok1) out[4:0] == 5'b0);

  // Coverage
  cover property (@(posedge clk) in==8'h00);
  cover property (@(posedge clk) in==8'h01);
  cover property (@(posedge clk) in==8'h02);
  cover property (@(posedge clk) in==8'h04);
  cover property (@(posedge clk) in==8'h08);
  cover property (@(posedge clk) in==8'h10);
  cover property (@(posedge clk) in==8'h20);
  cover property (@(posedge clk) in==8'h40);
  cover property (@(posedge clk) !valid_enc(in));              // invalid path (including 8'h80, multi-ones)
  cover property (@(posedge clk) disable iff (!ok2) (^$past(in,2)==1'b0 && out[8]==1'b1)); // even -> parity 1
  cover property (@(posedge clk) disable iff (!ok2) (^$past(in,2)==1'b1 && out[8]==1'b0)); // odd  -> parity 0

endmodule