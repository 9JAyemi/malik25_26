module binary_to_gray_sva (
    input logic [3:0] in,
    input logic load,
    output logic [3:0] out,
    output logic valid
);
    // Binary to Gray conversion on load
    binary_to_gray_conversion: assert property (
        @(posedge load) disable iff (!load) (out == (in >> 1) ^ in)
    );
    // Valid signal should be high only when load is high
    valid_signal: assert property (
        @(posedge load) disable iff (!load) (valid == 1'b1)
    );
    // Valid signal should be low when load is low
    valid_signal_low: assert property (
        @(posedge load) disable iff (load) (valid == 1'b0)
    );
endmodule