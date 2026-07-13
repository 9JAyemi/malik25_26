module mux6to1_pipeline_assertions (
    input logic       clk,
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [3:0] out
);

    // sel=000 drives out from the OR of data0 and data1.
    check_sel_000_or_data0_data1: assert property (
        @(posedge clk) (sel == 3'b000) |-> (out == (data0 | data1))
    );

    // sel=001 uses the same effective data0/data1 OR result.
    check_sel_001_or_data0_data1: assert property (
        @(posedge clk) (sel == 3'b001) |-> (out == (data0 | data1))
    );

    // sel=010 drives out from replicated OR of data2[3] and data3[3].
    check_sel_010_replicated_msb_or: assert property (
        @(posedge clk) (sel == 3'b010) |-> (out == {4{data2[3] | data3[3]}})
    );

    // sel=011 drives out from replicated OR of data2[0] and data3[0].
    check_sel_011_replicated_lsb_or: assert property (
        @(posedge clk) (sel == 3'b011) |-> (out == {4{data2[0] | data3[0]}})
    );

    // sel=100 forces the output to zero.
    check_sel_100_forces_zero: assert property (
        @(posedge clk) (sel == 3'b100) |-> (out == 4'b0000)
    );

    // Unhandled sel values drive zero.
    check_sel_default_forces_zero: assert property (
        @(posedge clk) ((sel == 3'b101) || (sel == 3'b110) || (sel == 3'b111)) |-> (out == 4'b0000)
    );

endmodule