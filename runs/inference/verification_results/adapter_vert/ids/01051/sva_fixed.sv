module ssio_sdr_in_sva (
    input logic clk_int,
    input logic clk_io,
    input logic input_clk,
    input logic input_d,
    input logic output_clk,
    input logic output_q,
    input logic BUFG,
    input logic BUFIO,
    input logic BUFIO2,
    input logic BUFR,
    input logic CLOCK_INPUT_STYLE
);

property ClockSynceotid; @(posedge input_clk) (input_clk) |-> (clk_int) && (clk_io); endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge input_clk) (input_clk) && (CLOCK_INPUT_STYLE == "BUFG") |-> (clk_int) && (clk_io); endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge input_clk) (input_clk) && (CLOCK_INPUT_STYLE == "BUFR") |-> (clk_int) && (clk_io) && (output_clk); endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge input_clk) (input_clk) && (CLOCK_INPUT_STYLE == "BUFIO") |-> (clk_int) && (clk_io) && (output_clk); endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(posedge input_clk) (input_clk) && (CLOCK_INPUT_STYLE == "BUFIO2") |-> (clk_int) && (clk_io) && (output_clk); endproperty
assert property (SyncIneotid_4);

property SyncIneotid_5; @(posedge input_clk) (input_clk) |-> (output_q) == (input_d); endproperty
assert property (SyncIneotid_5);

endmodule