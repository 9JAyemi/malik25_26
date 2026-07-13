module wasca_hexdot_sva (
    input logic clk,
    input logic reset_n,
    input logic [1:0] address,
    input logic chipselect,
    input logic write_n,
    input logic [31:0] writedata,
    output logic [5:0] out_port,
    output logic [31:0] readdata
);
    // Clock enable is always high
    property clk_enable;
        @(posedge clk) disable iff (!reset_n) clk_en == 1'b1;
    endproperty
    assert property (clk_enable) else $error("Clock enable is not always high");

    // Data_out is reset to 0 on reset
    property reset_data_out;
        @(posedge clk) disable iff (!reset_n) reset_n |-> data_out == 0;
    endproperty
    assert property (reset_data_out) else $error("Data_out is not reset to 0 on reset");

    // Data_out is updated on write operation
    property write_update;
        @(posedge clk) disable iff (!reset_n) chipselect && ~write_n && (address == 0) |-> data_out == writedata[5:0];
    endproperty
    assert property (write_update) else $error("Data_out is not updated on write operation");

    // Readdata is always 0
    property readdata_zero;
        @(posedge clk) disable iff (!reset_n) readdata == 32'b0;
    endproperty
    assert property (readdata_zero) else $error("Readdata is not always 0");

    // Out_port is equal to data_out
    property out_port_match;
        @(posedge clk) disable iff (!reset_n) out_port == data_out;
    endproperty
    assert property (out_port_match) else $error("Out_port is not equal to data_out");

    // Read_mux_out is 0 when address is not 0
    property read_mux_out_zero;
        @(posedge clk) disable iff (!reset_n) address != 0 |-> read_mux_out == 6'b0;
    endproperty
    assert property (read_mux_out_zero) else $error("Read_mux_out is not 0 when address is not 0");

    // Read_mux_out is data_out when address is 0
    property read_mux_out_match;
        @(posedge clk) disable iff (!reset_n) address == 0 |-> read_mux_out == data_out;
    endproperty
    assert property (read_mux_out_match) else $error("Read_mux_out is not equal to data_out when address is 0");

    // Readdata is read_mux_out
    property readdata_match;
        @(posedge clk) disable iff (!reset_n) readdata == read_mux_out;
    endproperty
    assert property (readdata_match) else $error("Readdata is not equal to read_mux_out");
endmodule