module mi_nios_cpu_nios2_oci_td_mode_sva (
    input logic clk,
    input logic [8:0] ctrl,
    input logic [3:0] td_mode
);
    // Local alias of mux select bits
    wire [2:0] ctrl_bits_for_mux = ctrl[7:5];

    // td_mode mapping when ctrl_bits_for_mux == 3'b000
    map_sel_000: assert property (
        @(posedge clk) (ctrl_bits_for_mux == 3'b000) |-> (td_mode == 4'b0000)
    );

    // td_mode mapping when ctrl_bits_for_mux == 3'b001
    map_sel_001: assert property (
        @(posedge clk) (ctrl_bits_for_mux == 3'b001) |-> (td_mode == 4'b1000)
    );

    // td_mode mapping when ctrl_bits_for_mux == 3'b010
    map_sel_010: assert property (
        @(posedge clk) (ctrl_bits_for_mux == 3'b010) |-> (td_mode == 4'b0100)
    );

    // td_mode mapping when ctrl_bits_for_mux == 3'b011
    map_sel_011: assert property (
        @(posedge clk) (ctrl_bits_for_mux == 3'b011) |-> (td_mode == 4'b1100)
    );

    // td_mode mapping when ctrl_bits_for_mux == 3'b100
    map_sel_100: assert property (
        @(posedge clk) (ctrl_bits_for_mux == 3'b100) |-> (td_mode == 4'b0010)
    );

    // td_mode mapping when ctrl_bits_for_mux == 3'b101
    map_sel_101: assert property (
        @(posedge clk) (ctrl_bits_for_mux == 3'b101) |-> (td_mode == 4'b1010)
    );

    // td_mode mapping when ctrl_bits_for_mux == 3'b110
    map_sel_110: assert property (
        @(posedge clk) (ctrl_bits_for_mux == 3'b110) |-> (td_mode == 4'b0101)
    );

    // td_mode mapping when ctrl_bits_for_mux == 3'b111
    map_sel_111: assert property (
        @(posedge clk) (ctrl_bits_for_mux == 3'b111) |-> (td_mode == 4'b1111)
    );

    // td_mode always matches the combinational decode of ctrl[7:5]
    decode_consistency: assert property (
        @(posedge clk)
            td_mode ==
            ((ctrl_bits_for_mux == 3'b000) ? 4'b0000 :
             (ctrl_bits_for_mux == 3'b001) ? 4'b1000 :
             (ctrl_bits_for_mux == 3'b010) ? 4'b0100 :
             (ctrl_bits_for_mux == 3'b011) ? 4'b1100 :
             (ctrl_bits_for_mux == 3'b100) ? 4'b0010 :
             (ctrl_bits_for_mux == 3'b101) ? 4'b1010 :
             (ctrl_bits_for_mux == 3'b110) ? 4'b0101 :
                                             4'b1111)
    );

    // td_mode can only be one of the enumerated decode values
    td_mode_range_check: assert property (
        @(posedge clk) td_mode inside {
            4'b0000, 4'b1000, 4'b0100, 4'b1100,
            4'b0010, 4'b1010, 4'b0101, 4'b1111
        }
    );
endmodule