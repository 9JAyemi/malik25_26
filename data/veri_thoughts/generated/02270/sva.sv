module mux6to1_pipeline_sva (
    input logic CLK,
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [3:0] out
);
    // When sel==000, out equals data0.
    check_sel_000_maps_to_data0: assert property (
        @(posedge CLK) (sel == 3'b000) |-> (out == data0)
    );

    // When sel==001, out equals data1.
    check_sel_001_maps_to_data1: assert property (
        @(posedge CLK) (sel == 3'b001) |-> (out == data1)
    );

    // When sel==010, out equals data2.
    check_sel_010_maps_to_data2: assert property (
        @(posedge CLK) (sel == 3'b010) |-> (out == data2)
    );

    // When sel==011, out equals data3.
    check_sel_011_maps_to_data3: assert property (
        @(posedge CLK) (sel == 3'b011) |-> (out == data3)
    );

    // When sel==100, out equals data4.
    check_sel_100_maps_to_data4: assert property (
        @(posedge CLK) (sel == 3'b100) |-> (out == data4)
    );

    // When sel==101, out equals data5.
    check_sel_101_maps_to_data5: assert property (
        @(posedge CLK) (sel == 3'b101) |-> (out == data5)
    );

    // When sel==110, out replicates data5[3] on all bits.
    check_sel_110_default_replication: assert property (
        @(posedge CLK) (sel == 3'b110) |-> (out == {4{data5[3]}})
    );

    // When sel==111, out replicates data5[3] on all bits.
    check_sel_111_default_replication: assert property (
        @(posedge CLK) (sel == 3'b111) |-> (out == {4{data5[3]}})
    );

    // Out implements the mux function including default replication.
    check_mux_function_full: assert property (
        @(posedge CLK)
        out == ((sel == 3'b000) ? data0 :
                (sel == 3'b001) ? data1 :
                (sel == 3'b010) ? data2 :
                (sel == 3'b011) ? data3 :
                (sel == 3'b100) ? data4 :
                (sel == 3'b101) ? data5 :
                                  {4{data5[3]}})
    );

    // If sel and inputs are stable, out is stable across cycles.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) $stable({sel, data0, data1, data2, data3, data4, data5}) |-> $stable(out)
    );
endmodule