module mux4to1_sva (
    input logic CLK,
    input logic data_in_0,
    input logic data_in_1,
    input logic data_in_2,
    input logic data_in_3,
    input logic ctrl_sel_0,
    input logic ctrl_sel_1,
    input logic data_out
);
    // When select is 00, output equals data_in_0.
    check_sel_00_maps_in0: assert property (
        @(posedge CLK) ({ctrl_sel_1, ctrl_sel_0} == 2'b00) |-> (data_out == data_in_0)
    );

    // When select is 01, output equals data_in_1.
    check_sel_01_maps_in1: assert property (
        @(posedge CLK) ({ctrl_sel_1, ctrl_sel_0} == 2'b01) |-> (data_out == data_in_1)
    );

    // When select is 10, output equals data_in_2.
    check_sel_10_maps_in2: assert property (
        @(posedge CLK) ({ctrl_sel_1, ctrl_sel_0} == 2'b10) |-> (data_out == data_in_2)
    );

    // When select is 11, output equals data_in_3.
    check_sel_11_maps_in3: assert property (
        @(posedge CLK) ({ctrl_sel_1, ctrl_sel_0} == 2'b11) |-> (data_out == data_in_3)
    );

    // Output equals the 4:1 mux function of select and inputs.
    check_functional_equivalence: assert property (
        @(posedge CLK) data_out == (ctrl_sel_1
                                    ? (ctrl_sel_0 ? data_in_3 : data_in_2)
                                    : (ctrl_sel_0 ? data_in_1 : data_in_0))
    );
endmodule