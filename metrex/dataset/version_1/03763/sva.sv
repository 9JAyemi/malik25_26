// SVA for excess_3_converter
// Bind this checker to the DUT

module excess_3_converter_sva (
  input logic [3:0] binary,
  input logic [7:0] excess_3
);

  default clocking cb @(binary or excess_3); endclocking

  function automatic logic [7:0] exp(input logic [3:0] b);
    return 8'd51 + {4'd0, b}; // 8'h33 + zero-extended binary
  endfunction

  // Functional correctness and range when input is known
  assert property ( !$isunknown(binary)
                    |-> ( !$isunknown(excess_3)
                          && excess_3 == exp(binary)
                          && (excess_3 inside {[8'h33:8'h42]}) ) )
    else $error("excess_3 mapping/range error: bin=%0d ex3=0x%0h", binary, excess_3);

  // Monotonic +1 relation across adjacent values
  assert property ( !$isunknown(binary) && !$isunknown($past(binary))
                    && (binary == $past(binary)+1)
                    |-> (!$isunknown(excess_3) && (excess_3 == $past(excess_3)+1)) )
    else $error("Monotonic +1 relation violated");

  // Any change in input must change output (injective mapping)
  assert property ( !$isunknown(binary) && !$isunknown($past(binary))
                    && (binary != $past(binary)) |-> (excess_3 != $past(excess_3)) )
    else $error("Output did not change when input changed");

  // Basic X-propagation check on output when input known
  assert property ( !$isunknown(binary) |-> !$isunknown(excess_3) )
    else $error("Output unknown with known input");

  // Coverage: hit all 16 input values
  genvar i;
  generate
    for (i=0; i<16; i++) begin : cv_bin
      cover property ( !$isunknown(binary) && (binary == i) );
    end
  endgenerate

  // Coverage: observe at least one +1 step
  cover property ( !$isunknown(binary) && !$isunknown($past(binary))
                   && (binary == $past(binary)+1)
                   && (excess_3 == $past(excess_3)+1) );

endmodule

bind excess_3_converter excess_3_converter_sva sva_i (.binary(binary), .excess_3(excess_3));