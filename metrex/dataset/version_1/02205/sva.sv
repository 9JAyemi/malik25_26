// SVA for adder_8bit
module adder_8bit_sva (
  input  logic [7:0] A,
  input  logic [7:0] B,
  input  logic       enable,
  input  logic [7:0] C
);

  // Post-delta immediate checks to avoid races with DUT combinational updates
  always @(A or B or enable or C) begin
    #0;
    if (!$isunknown({A,B,enable})) begin
      assert (C == (enable ? (A + B) : 8'h00))
        else $error("adder_8bit mismatch: A=%0h B=%0h en=%0b C=%0h exp=%0h",
                    A, B, enable, C, (enable ? (A + B) : 8'h00));
      assert (!$isunknown(C))
        else $error("adder_8bit produced X/Z on C with known inputs");
    end
  end

  // Simple covers to ensure both branches and key corner cases are hit
  // Enable/disable observed
  cover property (@(posedge enable) 1);
  cover property (@(negedge enable) 1);

  // Enabled path exercised with/without overflow
  cover property (@(A or B or enable) ##0 (enable && !({1'b0,A}+{1'b0,B})[8] && (C == (A + B))));
  cover property (@(A or B or enable) ##0 (enable &&  ({1'b0,A}+{1'b0,B})[8] && (C == (A + B))));

  // Disabled path holds zero even when inputs non-zero
  cover property (@(A or B or enable) ##0 (!enable && (A!=8'h0 || B!=8'h0) && (C == 8'h00)));

  // Enabled path produces zero sum case (e.g., 0+0 or wrap to 0)
  cover property (@(A or B or enable) ##0 (enable && (C == 8'h00)));
endmodule

bind adder_8bit adder_8bit_sva u_adder_8bit_sva (.A(A), .B(B), .enable(enable), .C(C));