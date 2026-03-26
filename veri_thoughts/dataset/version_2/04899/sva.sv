module barrel_shifter_assertions (
    input logic        clk,
    input logic [15:0] data,
    input logic [3:0]  shift_amount,
    input logic        direction,
    input logic [15:0] q
);

    function automatic [15:0] rot_left16(input [15:0] d, input [3:0] s);
        begin
            case (s)
                4'b0000: rot_left16 = d;
                4'b0001: rot_left16 = {d[14:0], d[15]};
                4'b0010: rot_left16 = {d[13:0], d[15:14]};
                4'b0011: rot_left16 = {d[12:0], d[15:13]};
                4'b0100: rot_left16 = {d[11:0], d[15:12]};
                4'b0101: rot_left16 = {d[10:0], d[15:11]};
                4'b0110: rot_left16 = {d[9:0], d[15:10]};
                4'b0111: rot_left16 = {d[8:0], d[15:9]};
                4'b1000: rot_left16 = {d[7:0], d[15:8]};
                4'b1001: rot_left16 = {d[6:0], d[15:7]};
                4'b1010: rot_left16 = {d[5:0], d[15:6]};
                4'b1011: rot_left16 = {d[4:0], d[15:5]};
                4'b1100: rot_left16 = {d[3:0], d[15:4]};
                4'b1101: rot_left16 = {d[2:0], d[15:3]};
                4'b1110: rot_left16 = {d[1:0], d[15:2]};
                4'b1111: rot_left16 = {d[0], d[15:1]};
                default: rot_left16 = d;
            endcase
        end
    endfunction

    function automatic [15:0] rot_right16(input [15:0] d, input [3:0] s);
        begin
            case (s)
                4'b0000: rot_right16 = d;
                4'b0001: rot_right16 = {d[0], d[15:1]};
                4'b0010: rot_right16 = {d[1:0], d[15:2]};
                4'b0011: rot_right16 = {d[2:0], d[15:3]};
                4'b0100: rot_right16 = {d[3:0], d[15:4]};
                4'b0101: rot_right16 = {d[4:0], d[15:5]};
                4'b0110: rot_right16 = {d[5:0], d[15:6]};
                4'b0111: rot_right16 = {d[6:0], d[15:7]};
                4'b1000: rot_right16 = {d[7:0], d[15:8]};
                4'b1001: rot_right16 = {d[8:0], d[15:9]};
                4'b1010: rot_right16 = {d[9:0], d[15:10]};
                4'b1011: rot_right16 = {d[10:0], d[15:11]};
                4'b1100: rot_right16 = {d[11:0], d[15:12]};
                4'b1101: rot_right16 = {d[12:0], d[15:13]};
                4'b1110: rot_right16 = {d[13:0], d[15:14]};
                4'b1111: rot_right16 = {d[14:0], d[15]};
                default: rot_right16 = d;
            endcase
        end
    endfunction

    // Left direction must match the implemented rotation table.
    check_left_rotation_table: assert property (
        @(posedge clk) (direction == 1'b1) |-> (q == rot_left16(data, shift_amount))
    );

    // Right direction must match the implemented rotation table.
    check_right_rotation_table: assert property (
        @(posedge clk) (direction == 1'b0) |-> (q == rot_right16(data, shift_amount))
    );

    // Left rotation by zero returns the input unchanged.
    check_left_shift_zero_identity: assert property (
        @(posedge clk) (direction == 1'b1) && (shift_amount == 4'b0000) |-> (q == data)
    );

    // Right rotation by zero returns the input unchanged.
    check_right_shift_zero_identity: assert property (
        @(posedge clk) (direction == 1'b0) && (shift_amount == 4'b0000) |-> (q == data)
    );

    // Left rotation by one wraps the MSB into bit 0.
    check_left_shift_one_wraps_msb: assert property (
        @(posedge clk) (direction == 1'b1) && (shift_amount == 4'b0001) |-> (q == {data[14:0], data[15]})
    );

    // Right rotation by one wraps the LSB into bit 15.
    check_right_shift_one_wraps_lsb: assert property (
        @(posedge clk) (direction == 1'b0) && (shift_amount == 4'b0001) |-> (q == {data[0], data[15:1]})
    );

    // Left rotation by eight swaps the upper and lower bytes.
    check_left_shift_eight_swaps_bytes: assert property (
        @(posedge clk) (direction == 1'b1) && (shift_amount == 4'b1000) |-> (q == {data[7:0], data[15:8]})
    );

    // Right rotation by eight swaps the upper and lower bytes.
    check_right_shift_eight_swaps_bytes: assert property (
        @(posedge clk) (direction == 1'b0) && (shift_amount == 4'b1000) |-> (q == {data[7:0], data[15:8]})
    );

    // Left rotation by fifteen matches the RTL wrap-around mapping.
    check_left_shift_fifteen_wraps: assert property (
        @(posedge clk) (direction == 1'b1) && (shift_amount == 4'b1111) |-> (q == {data[0], data[15:1]})
    );

    // Right rotation by fifteen matches the RTL wrap-around mapping.
    check_right_shift_fifteen_wraps: assert property (
        @(posedge clk) (direction == 1'b0) && (shift_amount == 4'b1111) |-> (q == {data[14:0], data[15]})
    );

    // Stable inputs must produce a stable output across sampled cycles.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({data, shift_amount, direction}) |-> $stable(q)
    );

endmodule