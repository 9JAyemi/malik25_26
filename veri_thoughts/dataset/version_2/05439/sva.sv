module sync_reset_set_register_sva #(
    parameter WIDTH = 8,
    parameter RESET_VALUE = 0
) (
    input logic [WIDTH-1:0] DataIn,
    input logic             Write,
    input logic             Set,
    input logic             Reset,
    input logic             Clk,
    input logic [WIDTH-1:0] DataOut
);

    localparam [WIDTH-1:0] RESET_CONST = RESET_VALUE;
    localparam [WIDTH-1:0] SET_CONST   = {WIDTH{1'b1}};

    // Reset loads the configured reset value.
    check_reset_loads_reset_value: assert property (
        @(posedge Clk) Reset |=> (DataOut == RESET_CONST)
    );

    // Set loads all ones when reset is not asserted.
    check_set_loads_all_ones: assert property (
        @(posedge Clk) disable iff (Reset) Set |=> (DataOut == SET_CONST)
    );

    // Write loads DataIn when neither reset nor set is asserted.
    check_write_loads_datain: assert property (
        @(posedge Clk) disable iff (Reset) (!Set && Write) |=> (DataOut == $past(DataIn))
    );

    // DataOut holds its value when no control is asserted.
    check_hold_when_idle: assert property (
        @(posedge Clk) disable iff (Reset) (!Set && !Write) |=> $stable(DataOut)
    );

    // Any observed output change must come from a prior update control.
    check_change_requires_prior_control: assert property (
        @(posedge Clk) disable iff ($initstate) (DataOut != $past(DataOut)) |-> $past(Reset || Set || Write)
    );

endmodule