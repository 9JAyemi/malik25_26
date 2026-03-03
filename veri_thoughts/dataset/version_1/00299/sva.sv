// SVA for mux4_reset
// Concise, high-quality checks with functional coverage. Bind this to the DUT.

module mux4_reset_sva (
  input        reset,
  input  [1:0] sel,
  input  [3:0] in0,
  input  [3:0] in1,
  input  [3:0] in2,
  input  [3:0] in3,
  input  [3:0] out
);

  // Basic X/Z sanitation on control
  always_comb begin
    assert (!$isunknown(reset)) else $error("mux4_reset: reset is X/Z");
    if (!reset) assert (!$isunknown(sel)) else $error("mux4_reset: sel is X/Z while reset=0");
  end

  // Functional correctness (masking on reset, muxing on sel)
  // Guarded to avoid false fires when control signals are X/Z
  always_comb begin
    if (!$isunknown(reset) && (reset || !$isunknown(sel))) begin
      assert #0 (
        reset ? (out === 4'b0000) :
        (sel==2'b00) ? (out === in0) :
        (sel==2'b01) ? (out === in1) :
        (sel==2'b10) ? (out === in2) :
                       (out === in3)
      ) else $error("mux4_reset: functional mismatch");
    end
  end

  // Coverage: hit reset assertion/deassertion and each select path while active
  cover property (@(posedge (reset==1'b1))) (out===4'b0000);
  cover property (@(negedge (reset==1'b1))) 1;

  cover property (@(posedge (!reset && (sel==2'b00)))) (out===in0);
  cover property (@(posedge (!reset && (sel==2'b01)))) (out===in1);
  cover property (@(posedge (!reset && (sel==2'b10)))) (out===in2);
  cover property (@(posedge (!reset && (sel==2'b11)))) (out===in3);

endmodule

// Bind into DUT
bind mux4_reset mux4_reset_sva mux4_reset_sva_i (.*);