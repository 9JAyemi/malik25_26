module sgpr_simx_rd_port_mux_sva (
    input logic        clk,
    input logic        port0_rd_en,
    input logic [8:0]  port0_rd_addr,
    input logic        port1_rd_en,
    input logic [8:0]  port1_rd_addr,
    input logic        port2_rd_en,
    input logic [8:0]  port2_rd_addr,
    input logic        port3_rd_en,
    input logic [8:0]  port3_rd_addr,
    input logic        port4_rd_en,
    input logic [8:0]  port4_rd_addr,
    input logic        port5_rd_en,
    input logic [8:0]  port5_rd_addr,
    input logic        port6_rd_en,
    input logic [8:0]  port6_rd_addr,
    input logic        port7_rd_en,
    input logic [8:0]  port7_rd_addr,
    input logic [31:0] port_rd_data,
    input logic [8:0]  rd_addr,
    input logic        rd_en,
    input logic [31:0] rd_data
);

    // port_rd_data is a direct pass-through of rd_data.
    check_port_rd_data_passthrough: assert property (
        @(posedge clk) port_rd_data === rd_data
    );

    // When only port0 is enabled, rd_addr selects port0 and rd_en is asserted.
    check_port0_select: assert property (
        @(posedge clk)
        ({port7_rd_en,port6_rd_en,port5_rd_en,port4_rd_en,port3_rd_en,port2_rd_en,port1_rd_en,port0_rd_en} === 8'b0000_0001)
        |-> ((rd_en === 1'b1) && (rd_addr === port0_rd_addr))
    );

    // When only port1 is enabled, rd_addr selects port1 and rd_en is asserted.
    check_port1_select: assert property (
        @(posedge clk)
        ({port7_rd_en,port6_rd_en,port5_rd_en,port4_rd_en,port3_rd_en,port2_rd_en,port1_rd_en,port0_rd_en} === 8'b0000_0010)
        |-> ((rd_en === 1'b1) && (rd_addr === port1_rd_addr))
    );

    // When only port2 is enabled, rd_addr selects port2 and rd_en is asserted.
    check_port2_select: assert property (
        @(posedge clk)
        ({port7_rd_en,port6_rd_en,port5_rd_en,port4_rd_en,port3_rd_en,port2_rd_en,port1_rd_en,port0_rd_en} === 8'b0000_0100)
        |-> ((rd_en === 1'b1) && (rd_addr === port2_rd_addr))
    );

    // When only port3 is enabled, rd_addr selects port3 and rd_en is asserted.
    check_port3_select: assert property (
        @(posedge clk)
        ({port7_rd_en,port6_rd_en,port5_rd_en,port4_rd_en,port3_rd_en,port2_rd_en,port1_rd_en,port0_rd_en} === 8'b0000_1000)
        |-> ((rd_en === 1'b1) && (rd_addr === port3_rd_addr))
    );

    // When only port4 is enabled, rd_addr selects port4 and rd_en is asserted.
    check_port4_select: assert property (
        @(posedge clk)
        ({port7_rd_en,port6_rd_en,port5_rd_en,port4_rd_en,port3_rd_en,port2_rd_en,port1_rd_en,port0_rd_en} === 8'b0001_0000)
        |-> ((rd_en === 1'b1) && (rd_addr === port4_rd_addr))
    );

    // When only port5 is enabled, rd_addr selects port5 and rd_en is asserted.
    check_port5_select: assert property (
        @(posedge clk)
        ({port7_rd_en,port6_rd_en,port5_rd_en,port4_rd_en,port3_rd_en,port2_rd_en,port1_rd_en,port0_rd_en} === 8'b0010_0000)
        |-> ((rd_en === 1'b1) && (rd_addr === port5_rd_addr))
    );

    // When only port6 is enabled, rd_addr selects port6 and rd_en is asserted.
    check_port6_select: assert property (
        @(posedge clk)
        ({port7_rd_en,port6_rd_en,port5_rd_en,port4_rd_en,port3_rd_en,port2_rd_en,port1_rd_en,port0_rd_en} === 8'b0100_0000)
        |-> ((rd_en === 1'b1) && (rd_addr === port6_rd_addr))
    );

    // When only port7 is enabled, rd_addr selects port7 and rd_en is asserted.
    check_port7_select: assert property (
        @(posedge clk)
        ({port7_rd_en,port6_rd_en,port5_rd_en,port4_rd_en,port3_rd_en,port2_rd_en,port1_rd_en,port0_rd_en} === 8'b1000_0000)
        |-> ((rd_en === 1'b1) && (rd_addr === port7_rd_addr))
    );

    // When no ports are enabled, rd_en is deasserted.
    check_no_port_enabled: assert property (
        @(posedge clk)
        ({port7_rd_en,port6_rd_en,port5_rd_en,port4_rd_en,port3_rd_en,port2_rd_en,port1_rd_en,port0_rd_en} === 8'b0000_0000)
        |-> (rd_en === 1'b0)
    );

endmodule