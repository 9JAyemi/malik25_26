// SVA for ParamModule
module ParamModule_sva (
    input logic         clk,
    input logic         reset_l,
    input logic [3:0]   param1,
    input logic [7:0]   param2,
    input logic [15:0]  param3,
    input logic [31:0]  result
);

    // Track when $past is valid
    logic past_valid;
    always_ff @(posedge clk) past_valid <= 1'b1;

    // Zero-extend and sum helper
    function automatic [31:0] sum32(input [3:0] p1, input [7:0] p2, input [15:0] p3);
        sum32 = {28'd0,p1} + {24'd0,p2} + {16'd0,p3};
    endfunction

    // Basic sanity: reset must not be X
    assert property (@(posedge clk) !$isunknown(reset_l))
      else $error("reset_l is X/Z");

    // When active, inputs must not be X/Z
    assert property (@(posedge clk) reset_l |-> !$isunknown({param1,param2,param3}))
      else $error("Inputs X/Z while active");

    // After a cycle with reset asserted, result must be 0
    assert property (@(posedge clk) past_valid && !$past(reset_l) |-> (result == 32'd0))
      else $error("Result not cleared after reset");

    // Functional update: result equals previous cycle's sum when not in reset
    assert property (@(posedge clk)
                     past_valid && $past(reset_l) && !$isunknown($past({param1,param2,param3}))
                     |-> result == sum32($past(param1), $past(param2), $past(param3)))
      else $error("Result does not match previous inputs' sum");

    // Result should not be X/Z in active operation
    assert property (@(posedge clk) past_valid && $past(reset_l) |-> !$isunknown(result))
      else $error("Result X/Z in active operation");

    // Optional: result always fits in 17 bits (given input widths)
    assert property (@(posedge clk) !$isunknown(result) |-> (result[31:17] == '0))
      else $error("Upper bits of result should be zero");

    // Coverage

    // See reset assert then deassert
    cover property (@(posedge clk) !reset_l ##1 reset_l);

    // See a non-zero sum update
    cover property (@(posedge clk)
                    past_valid && $past(reset_l) && $past(|{param1,param2,param3})
                    |-> (result != 32'd0));

    // See maximum input combination produce expected sum
    cover property (@(posedge clk)
                    past_valid &&
                    $past(reset_l) &&
                    $past(param1==4'hF && param2==8'hFF && param3==16'hFFFF) &&
                    result == sum32(4'hF, 8'hFF, 16'hFFFF));

    // See zero inputs produce zero result in active mode
    cover property (@(posedge clk)
                    past_valid && $past(reset_l) && $past({param1,param2,param3} == '0) &&
                    result == 32'd0);

endmodule

// Bind to the DUT
bind ParamModule ParamModule_sva sva_i (
    .clk    (clk),
    .reset_l(reset_l),
    .param1 (param1),
    .param2 (param2),
    .param3 (param3),
    .result (result)
);