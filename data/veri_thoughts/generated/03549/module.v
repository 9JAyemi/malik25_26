module three_input_op (
    output reg Y,
    input A,
    input B,
    input C,
    input [1:0] op,
    input sel
);

    reg [2:0] input_signals;
    reg [1:0] selected_signals;
    reg [2:0] and_results;
    reg [2:0] or_results;
    reg [2:0] xor_results;
    reg [2:0] xnor_results;

    // Assign the input signals based on the sel signal
    always @* begin
        case (sel)
            0: begin
                input_signals[0] = A;
                input_signals[1] = B;
                input_signals[2] = B;
            end
            1: begin
                input_signals[0] = B;
                input_signals[1] = B;
                input_signals[2] = C;
            end
        endcase
    end

    // Perform the AND operation on the input signals
    always @* begin
        and_results[0] = input_signals[0] & input_signals[1];
        and_results[1] = input_signals[1] & input_signals[2];
        and_results[2] = input_signals[2] & input_signals[0];
    end

    // Perform the OR operation on the input signals
    always @* begin
        or_results[0] = input_signals[0] | input_signals[1];
        or_results[1] = input_signals[1] | input_signals[2];
        or_results[2] = input_signals[2] | input_signals[0];
    end

    // Perform the XOR operation on the input signals
    always @* begin
        xor_results[0] = input_signals[0] ^ input_signals[1];
        xor_results[1] = input_signals[1] ^ input_signals[2];
        xor_results[2] = input_signals[2] ^ input_signals[0];
    end

    // Perform the XNOR operation on the input signals
    always @* begin
        xnor_results[0] = ~(input_signals[0] ^ input_signals[1]);
        xnor_results[1] = ~(input_signals[1] ^ input_signals[2]);
        xnor_results[2] = ~(input_signals[2] ^ input_signals[0]);
    end

    // Determine which two input signals to use based on the sel signal
    always @* begin
        selected_signals = (sel == 0) ? 2'b00 : 2'b10;
    end

    // Perform the operation based on the op signal
    always @* begin
        case (op)
            2'b00: Y = and_results[selected_signals];
            2'b01: Y = or_results[selected_signals];
            2'b10: Y = xor_results[selected_signals];
            2'b11: Y = xnor_results[selected_signals];
            default: Y = 1'b0;
        endcase
    end

endmodule