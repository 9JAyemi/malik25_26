// SVA for binary_to_gray
// Checks spec: gray = binary ^ (binary >> 1), no X on outputs, plus concise coverage.

module binary_to_gray_sva (input logic [3:0] binary,
                           input logic [3:0] gray);

  // Sample on any input change; use ##0 to evaluate after combinational settles
  default clocking cb @(binary[0] or binary[1] or binary[2] or binary[3]); endclocking

  // Spec check: Gray = b ^ (b>>1)
  property p_gray_spec;
    1 |-> ##0 ( gray == {binary[3], (binary[3:1] ^ binary[2:0])} );
  endproperty
  assert property (p_gray_spec)
    else $error("Spec mismatch: gray=%b expected=%b binary=%b",
                gray, {binary[3], (binary[3:1] ^ binary[2:0])}, binary);

  // If inputs are 2-state, outputs must be 2-state
  assert property ( !$isunknown(binary) |-> ##0 !$isunknown(gray) )
    else $error("X/Z on gray for binary=%b", binary);

  // If binary increments by +1 (mod 16), Gray must change by exactly 1 bit
  assert property ( (binary == $past(binary) + 4'b0001) |-> $onehot(gray ^ $past(gray)) )
    else $error("+1 step not one-bit Gray change: b_past=%b b=%b g_past=%b g=%b",
                $past(binary), binary, $past(gray), gray);

  // Coverage: hit all 16 input codes
  genvar v;
  generate
    for (v=0; v<16; v++) begin : C_BIN_ALL
      cover property ( binary == v[3:0] );
    end
  endgenerate

  // Coverage: each gray bit toggles both ways at least once
  genvar i;
  generate
    for (i=0; i<4; i++) begin : C_GRAY_TOGGLES
      cover property ( $rose(gray[i]) );
      cover property ( $fell(gray[i]) );
    end
  endgenerate

  // Coverage: observe at least one +1 increment on binary
  cover property ( binary == $past(binary) + 4'b0001 );

endmodule

bind binary_to_gray binary_to_gray_sva sva_inst (.*);