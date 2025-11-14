// SVA checker for top_module
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  in,
  input logic [4:0]  shift_amount,
  input logic [7:0]  shifted_out,
  input logic        zero_flag,
  input logic [2:0]  pe_out,            // internal wire from priority_encoder
  input logic [2:0]  pe_out_internal    // registered copy in top
);

  // Default clock for concurrent assertions
  default clocking cb @(posedge clk); endclocking

  // -----------------------
  // Barrel shifter checking
  // -----------------------
  // Functional correctness for all legal shifts (0..7)
  assert property (shift_amount <= 5'd7 |-> shifted_out == (in << shift_amount))
    else $error("barrel_shifter mismatch for shift_amount 0..7");

  // For shifts >= 8, output must be zero
  assert property (shift_amount >= 5'd8 |-> shifted_out == 8'h00)
    else $error("barrel_shifter mismatch for shift_amount >= 8");

  // -----------------------
  // Zero flag checking
  // -----------------------
  assert property (zero_flag == (shifted_out == 8'h00))
    else $error("zero_flag must reflect shifted_out==0");

  // -----------------------
  // Priority encoder checking (combinational pe_out)
  // Priority is lowest index among bits [6:0]; bit7 maps to default 000
  // -----------------------
  // If bit 0 set => 001
  assert property (in[0] |-> pe_out == 3'b001)
    else $error("priority_encoder: in[0] not encoded as 001");

  // If bit i set and all lower bits clear => i+1
  assert property (in[1] && (in[0]   == 1'b0)                  |-> pe_out == 3'b010)
    else $error("priority_encoder: in[1] not encoded as 010");
  assert property (in[2] && (in[1:0] == 2'b00)                  |-> pe_out == 3'b011)
    else $error("priority_encoder: in[2] not encoded as 011");
  assert property (in[3] && (in[2:0] == 3'b000)                 |-> pe_out == 3'b100)
    else $error("priority_encoder: in[3] not encoded as 100");
  assert property (in[4] && (in[3:0] == 4'b0000)                |-> pe_out == 3'b101)
    else $error("priority_encoder: in[4] not encoded as 101");
  assert property (in[5] && (in[4:0] == 5'b00000)               |-> pe_out == 3'b110)
    else $error("priority_encoder: in[5] not encoded as 110");
  assert property (in[6] && (in[5:0] == 6'b000000)              |-> pe_out == 3'b111)
    else $error("priority_encoder: in[6] not encoded as 111");

  // If none of bits [6:0] are set (regardless of in[7]), out must be 000
  assert property ((in[6:0] == 7'b0) |-> pe_out == 3'b000)
    else $error("priority_encoder: default case not 000");

  // If any of bits [6:0] are set, out must not be 000
  assert property ((in[6:0] != 7'b0) |-> pe_out != 3'b000)
    else $error("priority_encoder: nonzero input encoded as 000");

  // -----------------------
  // pe_out_internal register behavior
  // -----------------------
  // On reset cycle, next cycle register is 0
  assert property (reset |=> pe_out_internal == 3'b000)
    else $error("pe_out_internal not cleared after reset");

  // When not in or coming from reset, register captures pe_out from previous cycle
  assert property (!reset && !$past(reset) |-> pe_out_internal == $past(pe_out))
    else $error("pe_out_internal does not match prior pe_out");

  // -----------------------
  // Coverage
  // -----------------------
  // Exercise all shift_amount cases
  cover property (shift_amount == 5'd0  && shifted_out == (in << 0));
  cover property (shift_amount == 5'd1  && shifted_out == (in << 1));
  cover property (shift_amount == 5'd2  && shifted_out == (in << 2));
  cover property (shift_amount == 5'd3  && shifted_out == (in << 3));
  cover property (shift_amount == 5'd4  && shifted_out == (in << 4));
  cover property (shift_amount == 5'd5  && shifted_out == (in << 5));
  cover property (shift_amount == 5'd6  && shifted_out == (in << 6));
  cover property (shift_amount == 5'd7  && shifted_out == (in << 7));
  cover property (shift_amount >= 5'd8  && shifted_out == 8'h00);

  // Zero flag 0/1
  cover property (zero_flag == 1'b0);
  cover property (zero_flag == 1'b1);

  // Priority encoder: each priority case hits
  cover property (in == 8'b0000_0001 && pe_out == 3'b001);
  cover property ((in[1] && !in[0])                 && pe_out == 3'b010);
  cover property ((in[2] && (in[1:0] == 2'b00))     && pe_out == 3'b011);
  cover property ((in[3] && (in[2:0] == 3'b000))    && pe_out == 3'b100);
  cover property ((in[4] && (in[3:0] == 4'b0000))   && pe_out == 3'b101);
  cover property ((in[5] && (in[4:0] == 5'b00000))  && pe_out == 3'b110);
  cover property ((in[6] && (in[5:0] == 6'b000000)) && pe_out == 3'b111);
  // Default covers both all-zero and bit7-only
  cover property (in == 8'b0000_0000 && pe_out == 3'b000);
  cover property (in == 8'b1000_0000 && pe_out == 3'b000);

  // Reset/deassertion sequence covered
  cover property (reset ##1 !reset);

endmodule

// Bind the checker to the DUT
bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .in(in),
  .shift_amount(shift_amount),
  .shifted_out(shifted_out),
  .zero_flag(zero_flag),
  .pe_out(pe_out),
  .pe_out_internal(pe_out_internal)
);