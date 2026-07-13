module priority_encoder_sva (
    input logic CLK,
    input logic [3:0] in,
    input logic [1:0] pos
);
    // in==1000 maps to pos==3.
    check_map_1000_to_3: assert property (
        @(posedge CLK) (in == 4'b1000) |-> (pos == 2'b11)
    );

    // in==0100 maps to pos==2.
    check_map_0100_to_2: assert property (
        @(posedge CLK) (in == 4'b0100) |-> (pos == 2'b10)
    );

    // in==0010 maps to pos==1.
    check_map_0010_to_1: assert property (
        @(posedge CLK) (in == 4'b0010) |-> (pos == 2'b01)
    );

    // in==0001 maps to pos==0.
    check_map_0001_to_0: assert property (
        @(posedge CLK) (in == 4'b0001) |-> (pos == 2'b00)
    );

    // All other inputs map to pos==0 (default case).
    check_default_maps_to_0: assert property (
        @(posedge CLK) (!(in inside {4'b1000,4'b0100,4'b0010,4'b0001})) |-> (pos == 2'b00)
    );

    // pos==3 can only occur when in==1000.
    check_pos_3_implies_1000: assert property (
        @(posedge CLK) (pos == 2'b11) |-> (in == 4'b1000)
    );

    // pos==2 can only occur when in==0100.
    check_pos_2_implies_0100: assert property (
        @(posedge CLK) (pos == 2'b10) |-> (in == 4'b0100)
    );

    // pos==1 can only occur when in==0010.
    check_pos_1_implies_0010: assert property (
        @(posedge CLK) (pos == 2'b01) |-> (in == 4'b0010)
    );

    // If input is stable, output remains stable.
    check_stable_in_keeps_pos_stable: assert property (
        @(posedge CLK) $stable(in) |-> $stable(pos)
    );
endmodule