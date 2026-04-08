module probe_decoder_sva (
    input logic        clk,
    input logic [63:0] probe0,
    input logic [63:0] probe1,
    input logic [15:0] device_out,
    input logic [47:0] action_out
);

    // device_out maps probe0 low 16 bits value 0x0001.
    check_device_decode_0001: assert property (
        @(posedge clk) (probe0[15:0] == 16'h0001) |=> (device_out == 16'h0001)
    );

    // device_out maps probe0 low 16 bits value 0x0002.
    check_device_decode_0002: assert property (
        @(posedge clk) (probe0[15:0] == 16'h0002) |=> (device_out == 16'h0002)
    );

    // device_out maps probe0 low 16 bits value 0x0003.
    check_device_decode_0003: assert property (
        @(posedge clk) (probe0[15:0] == 16'h0003) |=> (device_out == 16'h0003)
    );

    // device_out maps probe0 low 16 bits value 0x0004.
    check_device_decode_0004: assert property (
        @(posedge clk) (probe0[15:0] == 16'h0004) |=> (device_out == 16'h0004)
    );

    // device_out defaults to 0xFFFF for all other probe0 low 16-bit values.
    check_device_decode_default: assert property (
        @(posedge clk)
        (probe0[15:0] != 16'h0001 &&
         probe0[15:0] != 16'h0002 &&
         probe0[15:0] != 16'h0003 &&
         probe0[15:0] != 16'h0004) |=> (device_out == 16'hFFFF)
    );

    // action_out maps probe1 low 48 bits value 0x000000000001.
    check_action_decode_000001: assert property (
        @(posedge clk) (probe1[47:0] == 48'h000000000001) |=> (action_out == 48'h000000000001)
    );

    // action_out maps probe1 low 48 bits value 0x000000000002.
    check_action_decode_000002: assert property (
        @(posedge clk) (probe1[47:0] == 48'h000000000002) |=> (action_out == 48'h000000000002)
    );

    // action_out maps probe1 low 48 bits value 0x000000000003.
    check_action_decode_000003: assert property (
        @(posedge clk) (probe1[47:0] == 48'h000000000003) |=> (action_out == 48'h000000000003)
    );

    // action_out maps probe1 low 48 bits value 0x000000000004.
    check_action_decode_000004: assert property (
        @(posedge clk) (probe1[47:0] == 48'h000000000004) |=> (action_out == 48'h000000000004)
    );

    // action_out maps probe1 low 48 bits value 0x000000000005.
    check_action_decode_000005: assert property (
        @(posedge clk) (probe1[47:0] == 48'h000000000005) |=> (action_out == 48'h000000000005)
    );

    // action_out maps probe1 low 48 bits value 0x000000000006.
    check_action_decode_000006: assert property (
        @(posedge clk) (probe1[47:0] == 48'h000000000006) |=> (action_out == 48'h000000000006)
    );

    // action_out defaults to all ones for all other probe1 low 48-bit values.
    check_action_decode_default: assert property (
        @(posedge clk)
        (probe1[47:0] != 48'h000000000001 &&
         probe1[47:0] != 48'h000000000002 &&
         probe1[47:0] != 48'h000000000003 &&
         probe1[47:0] != 48'h000000000004 &&
         probe1[47:0] != 48'h000000000005 &&
         probe1[47:0] != 48'h000000000006) |=> (action_out == 48'hFFFFFFFFFFFF)
    );

endmodule