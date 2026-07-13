module MUX16X4_sva (
    input logic        clk,
    input logic [15:0] iInput0,
    input logic [15:0] iInput1,
    input logic [15:0] iInput2,
    input logic [15:0] iInput3,
    input logic [1:0]  iSelect,
    input logic [15:0] oOutput
);

    // Select 00 routes iInput0 to oOutput.
    check_select_00_routes_input0: assert property (
        @(posedge clk) (iSelect == 2'b00) |-> (oOutput == iInput0)
    );

    // Select 01 routes iInput1 to oOutput.
    check_select_01_routes_input1: assert property (
        @(posedge clk) (iSelect == 2'b01) |-> (oOutput == iInput1)
    );

    // Select 10 routes iInput2 to oOutput.
    check_select_10_routes_input2: assert property (
        @(posedge clk) (iSelect == 2'b10) |-> (oOutput == iInput2)
    );

    // Select 11 routes iInput3 to oOutput.
    check_select_11_routes_input3: assert property (
        @(posedge clk) (iSelect == 2'b11) |-> (oOutput == iInput3)
    );

endmodule