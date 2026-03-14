module mux_4to1_sva (
    input logic [3:0] data_in,
    input logic [1:0] sel,
    input logic       out
);
    // Out matches truth table at sel[0] rising edges.
    check_truth_table_on_sel0: assert property (
        @(posedge sel[0]) out == ((sel == 2'b00) ? data_in[0] :
                                   (sel == 2'b01) ? data_in[3] :
                                   1'b0)
    );

    // Out matches truth table at sel[1] rising edges.
    check_truth_table_on_sel1: assert property (
        @(posedge sel[1]) out == ((sel == 2'b00) ? data_in[0] :
                                   (sel == 2'b01) ? data_in[3] :
                                   1'b0)
    );

    // When sel==00, out equals data_in[0] at data_in[0] edges.
    check_sel00_data0_drives_out: assert property (
        @(posedge data_in[0]) (sel == 2'b00) |-> (out == data_in[0])
    );

    // When sel==01, out equals data_in[3] at data_in[3] edges.
    check_sel01_data3_drives_out: assert property (
        @(posedge data_in[3]) (sel == 2'b01) |-> (out == data_in[3])
    );

    // sel[1]==1 implies out is 0 at sel[1] rising edge (default case).
    check_default_zero_on_sel1_rise: assert property (
        @(posedge sel[1]) out == 1'b0
    );

    // Out cannot rise when sel[1]==1.
    check_no_out_rise_when_sel1_high: assert property (
        @(posedge out) sel[1] == 1'b0
    );
endmodule