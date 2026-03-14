module mux4_sva (
    input logic [3:0] data_in,
    input logic [1:0] select,
    input logic out
);
    // Output equals selected input when select[0] rises.
    check_mapping_on_sel0_rise: assert property (
        @(posedge select[0]) out == data_in[select]
    );

    // Output equals selected input when select[1] rises.
    check_mapping_on_sel1_rise: assert property (
        @(posedge select[1]) out == data_in[select]
    );

    // Output equals selected input when data_in[0] rises.
    check_mapping_on_data0_rise: assert property (
        @(posedge data_in[0]) out == data_in[select]
    );

    // Output equals selected input when data_in[1] rises.
    check_mapping_on_data1_rise: assert property (
        @(posedge data_in[1]) out == data_in[select]
    );

    // Output equals selected input when data_in[2] rises.
    check_mapping_on_data2_rise: assert property (
        @(posedge data_in[2]) out == data_in[select]
    );

    // Output equals selected input when data_in[3] rises.
    check_mapping_on_data3_rise: assert property (
        @(posedge data_in[3]) out == data_in[select]
    );

    // Output equals selected input when out rises.
    check_mapping_on_out_rise: assert property (
        @(posedge out) out == data_in[select]
    );
endmodule