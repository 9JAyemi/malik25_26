
module digital_lock (
    input [3:0] code, // 4-digit binary code input
    output reg open // Output signal indicating whether the lock is open or not
);

    // Define the stored password
    reg [3:0] password = 4'b0001;

    // Define the control logic
    reg state = 1'b0;
    always @ (code) begin
        if (code == 4'b0000) state <= ~state;
    end

    // Define the decoder and multiplexer module
    wire password_bit;
    assign password_bit = (state) ? password[0] : password[1];

    // Define the 8-bit adder module
    reg [7:0] sum;
    always @ (*) begin
        sum = {4'b0, code} + {4'b0, password_bit};
    end

    // Define the output logic
    always @ (sum) begin
        if (sum == 8'b00000000) open <= 1'b1;
        else open <= 1'b0;
    end

endmodule