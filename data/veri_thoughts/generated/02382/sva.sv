module my_module_sva (
    input logic clk,
    input logic [7:0] di,
    input logic [7:0] \do 
);
    // do[0] must equal di[0]
    check_do0_passthrough: assert property (
        @(posedge clk) \do [0] == di[0]
    );
    // do[1] must equal di[1]
    check_do1_passthrough: assert property (
        @(posedge clk) \do [1] == di[1]
    );
    // do[2] must equal di[2]
    check_do2_passthrough: assert property (
        @(posedge clk) \do [2] == di[2]
    );
    // do[3] must equal di[3]
    check_do3_passthrough: assert property (
        @(posedge clk) \do [3] == di[3]
    );
    // do[4] must equal di[4]
    check_do4_passthrough: assert property (
        @(posedge clk) \do [4] == di[4]
    );
    // do[5] must be logical NOT of di[5]
    check_do5_invert: assert property (
        @(posedge clk) \do [5] == ~di[5]
    );
    // do[6] must be logical NOT of di[6]
    check_do6_invert: assert property (
        @(posedge clk) \do [6] == ~di[6]
    );
    // do[7] must be logical NOT of di[7]
    check_do7_invert: assert property (
        @(posedge clk) \do [7] == ~di[7]
    );
    // Lower 5 bits collectively pass through
    check_lower_bus_passthrough: assert property (
        @(posedge clk) \do [4:0] == di[4:0]
    );
    // Upper 3 bits collectively invert
    check_upper_bus_invert: assert property (
        @(posedge clk) \do [7:5] == ~di[7:5]
    );
    // Full byte mapping matches spec
    check_full_byte_mapping: assert property (
        @(posedge clk) \do  == {~di[7:5], di[4:0]}
    );
endmodule