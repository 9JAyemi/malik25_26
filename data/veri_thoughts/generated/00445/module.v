module interstage_buffer_if_id(
    input clock,
    input [3:0] if_control_signals,
    output reg [3:0] id_control_signals
);

    always @(posedge clock) begin
        id_control_signals <= if_control_signals;
    end

endmodule