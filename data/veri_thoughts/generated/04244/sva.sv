module DivSelSlice_sva (
    input logic clk,
    input logic [3:0] DivLenSel,
    input logic [8:0] DNB,
    input logic [8:0] DSN,
    input logic [8:0] Division
);

    // RTL has no native clock or reset; clk is a sampling clock for these checks.

    // Division[0] matches the implemented mux equation with DivLenSel[0].
    check_division0_equation: assert property (
        @(posedge clk)
        Division[0] === ((DNB[0] & DivLenSel[0]) | (DSN[0] & ~DNB[0]))
    );

    // Division[1] matches the implemented mux equation with DivLenSel[0].
    check_division1_equation: assert property (
        @(posedge clk)
        Division[1] === ((DNB[1] & DivLenSel[0]) | (DSN[1] & ~DNB[1]))
    );

    // Division[2] matches the implemented mux equation with DivLenSel[1].
    check_division2_equation: assert property (
        @(posedge clk)
        Division[2] === ((DNB[2] & DivLenSel[1]) | (DSN[2] & ~DNB[2]))
    );

    // Division[3] matches the implemented mux equation with DivLenSel[1].
    check_division3_equation: assert property (
        @(posedge clk)
        Division[3] === ((DNB[3] & DivLenSel[1]) | (DSN[3] & ~DNB[3]))
    );

    // Division[4] matches the implemented mux equation with DivLenSel[2].
    check_division4_equation: assert property (
        @(posedge clk)
        Division[4] === ((DNB[4] & DivLenSel[2]) | (DSN[4] & ~DNB[4]))
    );

    // Division[5] matches the implemented mux equation with DivLenSel[2].
    check_division5_equation: assert property (
        @(posedge clk)
        Division[5] === ((DNB[5] & DivLenSel[2]) | (DSN[5] & ~DNB[5]))
    );

    // Division[6] matches the implemented mux equation with DivLenSel[3].
    check_division6_equation: assert property (
        @(posedge clk)
        Division[6] === ((DNB[6] & DivLenSel[3]) | (DSN[6] & ~DNB[6]))
    );

    // Division[7] matches the implemented mux equation with DivLenSel[3].
    check_division7_equation: assert property (
        @(posedge clk)
        Division[7] === ((DNB[7] & DivLenSel[3]) | (DSN[7] & ~DNB[7]))
    );

    // Division[8] matches the implemented mux equation with DivLenSel[3].
    check_division8_equation: assert property (
        @(posedge clk)
        Division[8] === ((DNB[8] & DivLenSel[3]) | (DSN[8] & ~DNB[8]))
    );

endmodule