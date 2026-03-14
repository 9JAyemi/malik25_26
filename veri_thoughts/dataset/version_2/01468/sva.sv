module sirv_spigpioport_1_sva (
    input logic clock,
    input logic reset,
    input logic io_spi_sck,
    input logic io_spi_dq_0_i,
    input logic io_spi_dq_0_o,
    input logic io_spi_dq_0_oe,
    input logic io_spi_dq_1_i,
    input logic io_spi_dq_1_o,
    input logic io_spi_dq_1_oe,
    input logic io_spi_dq_2_i,
    input logic io_spi_dq_2_o,
    input logic io_spi_dq_2_oe,
    input logic io_spi_dq_3_i,
    input logic io_spi_dq_3_o,
    input logic io_spi_dq_3_oe,
    input logic io_spi_cs_0,
    input logic io_pins_sck_i_ival,
    input logic io_pins_sck_o_oval,
    input logic io_pins_sck_o_oe,
    input logic io_pins_sck_o_ie,
    input logic io_pins_sck_o_pue,
    input logic io_pins_sck_o_ds,
    input logic io_pins_dq_0_i_ival,
    input logic io_pins_dq_0_o_oval,
    input logic io_pins_dq_0_o_oe,
    input logic io_pins_dq_0_o_ie,
    input logic io_pins_dq_0_o_pue,
    input logic io_pins_dq_0_o_ds,
    input logic io_pins_dq_1_i_ival,
    input logic io_pins_dq_1_o_oval,
    input logic io_pins_dq_1_o_oe,
    input logic io_pins_dq_1_o_ie,
    input logic io_pins_dq_1_o_pue,
    input logic io_pins_dq_1_o_ds,
    input logic io_pins_dq_2_i_ival,
    input logic io_pins_dq_2_o_oval,
    input logic io_pins_dq_2_o_oe,
    input logic io_pins_dq_2_o_ie,
    input logic io_pins_dq_2_o_pue,
    input logic io_pins_dq_2_o_ds,
    input logic io_pins_dq_3_i_ival,
    input logic io_pins_dq_3_o_oval,
    input logic io_pins_dq_3_o_oe,
    input logic io_pins_dq_3_o_ie,
    input logic io_pins_dq_3_o_pue,
    input logic io_pins_dq_3_o_ds,
    input logic io_pins_cs_0_i_ival,
    input logic io_pins_cs_0_o_oval,
    input logic io_pins_cs_0_o_oe,
    input logic io_pins_cs_0_o_ie,
    input logic io_pins_cs_0_o_pue,
    input logic io_pins_cs_0_o_ds
);
    // DQ0 input reflects pin input value
    check_dq0_i_passthrough: assert property (
        @(posedge clock) disable iff (reset) (io_spi_dq_0_i == io_pins_dq_0_i_ival)
    );
    // DQ1 input reflects pin input value
    check_dq1_i_passthrough: assert property (
        @(posedge clock) disable iff (reset) (io_spi_dq_1_i == io_pins_dq_1_i_ival)
    );
    // DQ2 input reflects pin input value
    check_dq2_i_passthrough: assert property (
        @(posedge clock) disable iff (reset) (io_spi_dq_2_i == io_pins_dq_2_i_ival)
    );
    // DQ3 input reflects pin input value
    check_dq3_i_passthrough: assert property (
        @(posedge clock) disable iff (reset) (io_spi_dq_3_i == io_pins_dq_3_i_ival)
    );

    // SCK pin output value equals SPI SCK
    check_sck_oval_map: assert property (
        @(posedge clock) disable iff (reset) (io_pins_sck_o_oval == io_spi_sck)
    );
    // SCK output enable is constant 1
    check_sck_oe_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_sck_o_oe == 1'b1)
    );
    // SCK input enable is constant 0
    check_sck_ie_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_sck_o_ie == 1'b0)
    );
    // SCK pull-up enable is constant 0
    check_sck_pue_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_sck_o_pue == 1'b0)
    );
    // SCK drive strength is constant 0
    check_sck_ds_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_sck_o_ds == 1'b0)
    );

    // DQ0 pin output value equals SPI DQ0 output
    check_dq0_oval_map: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_0_o_oval == io_spi_dq_0_o)
    );
    // DQ0 output enable equals SPI DQ0 OE
    check_dq0_oe_map: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_0_o_oe == io_spi_dq_0_oe)
    );
    // DQ0 input enable is complement of SPI DQ0 OE
    check_dq0_ie_compl: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_0_o_ie == ~io_spi_dq_0_oe)
    );
    // DQ0 pull-up enable is constant 1
    check_dq0_pue_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_0_o_pue == 1'b1)
    );
    // DQ0 drive strength is constant 0
    check_dq0_ds_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_0_o_ds == 1'b0)
    );
    // DQ0 IE and OE are complementary
    check_dq0_ie_oe_mutex: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_0_o_ie == ~io_pins_dq_0_o_oe)
    );

    // DQ1 pin output value equals SPI DQ1 output
    check_dq1_oval_map: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_1_o_oval == io_spi_dq_1_o)
    );
    // DQ1 output enable equals SPI DQ1 OE
    check_dq1_oe_map: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_1_o_oe == io_spi_dq_1_oe)
    );
    // DQ1 input enable is complement of SPI DQ1 OE
    check_dq1_ie_compl: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_1_o_ie == ~io_spi_dq_1_oe)
    );
    // DQ1 pull-up enable is constant 1
    check_dq1_pue_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_1_o_pue == 1'b1)
    );
    // DQ1 drive strength is constant 0
    check_dq1_ds_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_1_o_ds == 1'b0)
    );
    // DQ1 IE and OE are complementary
    check_dq1_ie_oe_mutex: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_1_o_ie == ~io_pins_dq_1_o_oe)
    );

    // DQ2 pin output value equals SPI DQ2 output
    check_dq2_oval_map: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_2_o_oval == io_spi_dq_2_o)
    );
    // DQ2 output enable equals SPI DQ2 OE
    check_dq2_oe_map: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_2_o_oe == io_spi_dq_2_oe)
    );
    // DQ2 input enable is complement of SPI DQ2 OE
    check_dq2_ie_compl: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_2_o_ie == ~io_spi_dq_2_oe)
    );
    // DQ2 pull-up enable is constant 1
    check_dq2_pue_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_2_o_pue == 1'b1)
    );
    // DQ2 drive strength is constant 0
    check_dq2_ds_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_2_o_ds == 1'b0)
    );
    // DQ2 IE and OE are complementary
    check_dq2_ie_oe_mutex: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_2_o_ie == ~io_pins_dq_2_o_oe)
    );

    // DQ3 pin output value equals SPI DQ3 output
    check_dq3_oval_map: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_3_o_oval == io_spi_dq_3_o)
    );
    // DQ3 output enable equals SPI DQ3 OE
    check_dq3_oe_map: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_3_o_oe == io_spi_dq_3_oe)
    );
    // DQ3 input enable is complement of SPI DQ3 OE
    check_dq3_ie_compl: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_3_o_ie == ~io_spi_dq_3_oe)
    );
    // DQ3 pull-up enable is constant 1
    check_dq3_pue_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_3_o_pue == 1'b1)
    );
    // DQ3 drive strength is constant 0
    check_dq3_ds_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_3_o_ds == 1'b0)
    );
    // DQ3 IE and OE are complementary
    check_dq3_ie_oe_mutex: assert property (
        @(posedge clock) disable iff (reset) (io_pins_dq_3_o_ie == ~io_pins_dq_3_o_oe)
    );

    // CS0 pin output value equals SPI CS0
    check_cs0_oval_map: assert property (
        @(posedge clock) disable iff (reset) (io_pins_cs_0_o_oval == io_spi_cs_0)
    );
    // CS0 output enable is constant 1
    check_cs0_oe_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_cs_0_o_oe == 1'b1)
    );
    // CS0 input enable is constant 0
    check_cs0_ie_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_cs_0_o_ie == 1'b0)
    );
    // CS0 pull-up enable is constant 0
    check_cs0_pue_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_cs_0_o_pue == 1'b0)
    );
    // CS0 drive strength is constant 0
    check_cs0_ds_const: assert property (
        @(posedge clock) disable iff (reset) (io_pins_cs_0_o_ds == 1'b0)
    );
endmodule