module LCD_Driver_sva (
    input logic clk,
    input logic [7:0] data,
    input logic RS,
    input logic RW,
    input logic E,
    input logic LCD_RS,
    input logic LCD_RW,
    input logic LCD_E,
    input logic [7:0] LCD_DATA
);

    // All LCD outputs are the prior cycle's sampled inputs.
    check_registered_outputs: assert property (
        @(posedge clk) disable iff ($initstate)
        {LCD_RS, LCD_RW, LCD_E, LCD_DATA} == $past({RS, RW, E, data})
    );

    // LCD_DATA captures data on each rising clock edge.
    check_data_capture: assert property (
        @(posedge clk) disable iff ($initstate)
        LCD_DATA == $past(data)
    );

    // LCD_RS captures RS on each rising clock edge.
    check_rs_capture: assert property (
        @(posedge clk) disable iff ($initstate)
        LCD_RS == $past(RS)
    );

    // LCD_RW captures RW on each rising clock edge.
    check_rw_capture: assert property (
        @(posedge clk) disable iff ($initstate)
        LCD_RW == $past(RW)
    );

    // LCD_E captures E on each rising clock edge.
    check_e_capture: assert property (
        @(posedge clk) disable iff ($initstate)
        LCD_E == $past(E)
    );

endmodule