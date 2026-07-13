module Immediate_Extend_sva (
    input logic CLK,
    input logic [15:0] data_out,
    input logic [2:0] load,
    input logic [15:0] data_in
);
    // load==0: sign-extend data_in[7:0] into data_out[15:0]
    check_load0_signext8: assert property (
        @(posedge CLK) (load == 3'd0) |-> (data_out == {{8{data_in[7]}}, data_in[7:0]})
    );

    // load==1: sign-extend data_in[3:0] into data_out[15:0]
    check_load1_signext4: assert property (
        @(posedge CLK) (load == 3'd1) |-> (data_out == {{12{data_in[3]}}, data_in[3:0]})
    );

    // load==2: sign-extend data_in[10:0] into data_out[15:0]
    check_load2_signext11: assert property (
        @(posedge CLK) (load == 3'd2) |-> (data_out == {{5{data_in[10]}}, data_in[10:0]})
    );

    // load==3: zero-extend data_in[3:0] into data_out[15:0]
    check_load3_zeroext4: assert property (
        @(posedge CLK) (load == 3'd3) |-> (data_out == {12'b0, data_in[3:0]})
    );

    // load==4: zero-extend data_in[7:0] into data_out[15:0]
    check_load4_zeroext8: assert property (
        @(posedge CLK) (load == 3'd4) |-> (data_out == {8'b0, data_in[7:0]})
    );

    // load==5: sign-extend data_in[4:0] into data_out[15:0]
    check_load5_signext5: assert property (
        @(posedge CLK) (load == 3'd5) |-> (data_out == {{11{data_in[4]}}, data_in[4:0]})
    );

    // load==6/7: zero-extend data_in[4:2] into data_out[15:0]
    check_load67_zeroext3_from_4to2: assert property (
        @(posedge CLK) (load inside {3'd6, 3'd7}) |-> (data_out == {13'b0, data_in[4:2]})
    );
endmodule