module mux_4to1_en_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic en,
    input logic clk,
    input logic rst_n
);
    // Mux output is 0 when enable is 0, regardless of input selection
    mux_output_zero_when_disabled: assert property (
        @(posedge clk) disable iff (!rst_n) (en == 1'b0) |-> (out == 4'b0000)
    );

    // Mux output is one of the inputs when enable is 1 and select is valid
    mux_output_valid_when_enabled: assert property (
        @(posedge clk) disable iff (!rst_n) (en == 1'b1) |-> 
        (sel == 2'b00) |-> (out == in0) ||
        (sel == 2'b01) |-> (out == in1) ||
        (sel == 2'b10) |-> (out == in2) ||
        (sel == 2'b11) |-> (out == in3)
    );

    // Mux output is 0 when select is invalid
    mux_output_zero_when_invalid_select: assert property (
        @(posedge clk) disable iff (!rst_n) (sel != 2'b00) && (sel != 2'b01) && (sel != 2'b10) && (sel != 2'b11) |-> (out == 4'b0000)
    );

    // Mux output is stable when enable is 0
    mux_output_stable_when_disabled: assert property (
        @(posedge clk) disable iff (!rst_n) (en == 1'b0) |-> $stable(out)
    );

    // Mux output is stable when select is invalid
    mux_output_stable_when_invalid_select: assert property (
        @(posedge clk) disable iff (!rst_n) (sel != 2'b00) && (sel != 2'b01) && (sel != 2'b10) && (sel != 2'b11) |-> $stable(out)
    );

    // Mux output is stable when enable is 1 and select is valid
    mux_output_stable_when_enabled: assert property (
        @(posedge clk) disable iff (!rst_n) (en == 1'b1) |-> 
        (sel == 2'b00) |-> $stable(out) ||
        (sel == 2'b01) |-> $stable(out) ||
        (sel == 2'b10) |-> $stable(out) ||
        (sel == 2'b11) |-> $stable(out)
    );

    // Mux output is 0 when reset is active
    mux_output_zero_when_reset_active: assert property (
        @(posedge clk) disable iff (rst_n) (rst_n == 1'b0) |-> (out == 4'b0000)
    );

endmodule