module manual (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q
);
    parameter WIDTH = 1;
    parameter RESET_VAL = 0;

    // Ensure that the reset value is applied correctly
    reset_value: assert property (
        @(posedge clk) disable iff (!rst) (q == RESET_VAL)
    ) else $error("Reset value not applied correctly");

    // Ensure that the output follows the enable signal
    enable_behavior: assert property (
        @(posedge clk) disable iff (!rst) (en |-> (q == d))
    ) else $error("Output does not follow enable signal");

    // Ensure that the output does not change when disabled
    disable_behavior: assert property (
        @(posedge clk) disable iff (!rst) (!en |-> (q == q))
    ) else $error("Output changes when disabled");

    // Ensure that the output is always equal to the input when enabled
    always_enabled: assert property (
        @(posedge clk) disable iff (!rst) (en |-> (q == d))
    ) else $error("Output is not always equal to the input when enabled");

    // Ensure that the output is always equal to the reset value when disabled
    always_disabled: assert property (
        @(posedge clk) disable iff (!rst) (!en |-> (q == RESET_VAL))
    ) else $error("Output is not always equal to the reset value when disabled");

    // Ensure that the output is always equal to the input when reset is active
    reset_active: assert property (
        @(posedge clk) disable iff (rst) (q == RESET_VAL)
    ) else $error("Output is not always equal to the reset value when reset is active");

    // Ensure that the output is always equal to the input when reset is inactive
    reset_inactive: assert property (
        @(posedge clk) disable iff (!rst) (q == d)
    ) else $error("Output is not always equal to the input when reset is inactive");

    // Ensure that the output is always equal to the input when enable is active
    enable_active: assert property (
        @(posedge clk) disable iff (!rst) (en |-> (q == d))
    ) else $error("Output is not always equal to the input when enable is active");

    // Ensure that the output is always equal to the input when enable is inactive
    enable_inactive: assert property (
        @(posedge clk) disable iff (!rst) (!en |-> (q == q))
    ) else $error("Output is not always equal to the input when enable is inactive");

    // Ensure that the output is always equal to the input when reset and enable are active
    reset_enable_active: assert property (
        @(posedge clk) disable iff (!rst) (rst |-> (q == RESET_VAL))
    ) else $error("Output is not always equal to the reset value when reset and enable are active");

    // Ensure that the output is always equal to the input when reset and enable are inactive
    reset_enable_inactive: assert property (
        @(posedge clk) disable iff (!rst) (!rst |-> (q == d))
    ) else $error("Output is not always equal to the input when reset and enable are inactive");
endmodule