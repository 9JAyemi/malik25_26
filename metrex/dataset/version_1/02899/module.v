
module dff_preset_clear (
    input wire D,
    input wire CLK,
    input wire PRE,  // Preset
    input wire CLR,  // Clear
    output wire Q,
    output wire Q_N
);

    reg [0:0] _Q;
    assign Q = _Q[0];
    assign Q_N = ~_Q[0];

    always @(posedge CLK) begin
        if (CLR) begin // Clear
            _Q[0] <= 0;
        end else if (PRE) begin // Preset
            _Q[0] <= 1;
        end else begin // Normal Operation
            _Q[0] <= D;
        end
    end

endmodule