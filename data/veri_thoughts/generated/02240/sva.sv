module mi_nios_cpu_nios2_oci_fifo_wrptr_inc_sva (
    input logic CLK,                      // sampling clock for assertions
    input logic ge2_free,
    input logic ge3_free,
    input logic [1:0] input_tm_cnt,
    input logic [3:0] fifo_wrptr_inc
);
    // input_tm_cnt==0 maps to 0
    check_cnt0_maps_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (input_tm_cnt == 2'd0) |-> (fifo_wrptr_inc == 4'b0000)
    );

    // input_tm_cnt==1 maps to 1
    check_cnt1_maps_one: assert property (
        @(posedge CLK) disable iff (1'b0) (input_tm_cnt == 2'd1) |-> (fifo_wrptr_inc == 4'b0001)
    );

    // input_tm_cnt==2 with ge2_free maps to 2
    check_cnt2_ge2_maps_two: assert property (
        @(posedge CLK) disable iff (1'b0) ((input_tm_cnt == 2'd2) && ge2_free) |-> (fifo_wrptr_inc == 4'b0010)
    );

    // input_tm_cnt==2 without ge2_free maps to 1
    check_cnt2_no_ge2_maps_one: assert property (
        @(posedge CLK) disable iff (1'b0) ((input_tm_cnt == 2'd2) && !ge2_free) |-> (fifo_wrptr_inc == 4'b0001)
    );

    // input_tm_cnt==3 with ge3_free maps to 3
    check_cnt3_ge3_maps_three: assert property (
        @(posedge CLK) disable iff (1'b0) ((input_tm_cnt == 2'd3) && ge3_free) |-> (fifo_wrptr_inc == 4'b0011)
    );

    // input_tm_cnt==3 without ge3_free but with ge2_free maps to 2
    check_cnt3_no_ge3_ge2_maps_two: assert property (
        @(posedge CLK) disable iff (1'b0) ((input_tm_cnt == 2'd3) && !ge3_free && ge2_free) |-> (fifo_wrptr_inc == 4'b0010)
    );

    // input_tm_cnt==3 without ge3_free and without ge2_free maps to 1
    check_cnt3_no_ge3_no_ge2_maps_one: assert property (
        @(posedge CLK) disable iff (1'b0) ((input_tm_cnt == 2'd3) && !ge3_free && !ge2_free) |-> (fifo_wrptr_inc == 4'b0001)
    );

    // Output encoding limited to 0..3
    check_out_value_domain: assert property (
        @(posedge CLK) disable iff (1'b0) fifo_wrptr_inc inside {4'b0000,4'b0001,4'b0010,4'b0011}
    );

    // If output is 3 then ge3_free and cnt==3 held
    check_out3_implies_ge3_cnt3: assert property (
        @(posedge CLK) disable iff (1'b0) (fifo_wrptr_inc == 4'b0011) |-> (ge3_free && (input_tm_cnt == 2'd3))
    );

    // If output is 2 then ge2_free and cnt>=2 and not (ge3_free && cnt==3)
    check_out2_implies_ge2_and_not_ge3cnt3: assert property (
        @(posedge CLK) disable iff (1'b0) (fifo_wrptr_inc == 4'b0010) |-> (ge2_free && (input_tm_cnt >= 2'd2) && !(ge3_free && (input_tm_cnt == 2'd3)))
    );

    // If output is 1 then cnt>=1 and neither higher-priority condition held
    check_out1_implies_no_higher_conditions: assert property (
        @(posedge CLK) disable iff (1'b0) (fifo_wrptr_inc == 4'b0001) |-> ((input_tm_cnt >= 2'd1) && !(ge3_free && (input_tm_cnt == 2'd3)) && !(ge2_free && (input_tm_cnt >= 2'd2)))
    );

    // If output is 0 then cnt==0
    check_out0_implies_cnt0: assert property (
        @(posedge CLK) disable iff (1'b0) (fifo_wrptr_inc == 4'b0000) |-> (input_tm_cnt == 2'd0)
    );
endmodule