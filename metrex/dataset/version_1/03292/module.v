
module password_protected_system (
    input clk,
    input d,
    input [255:0] password,
    input [2:0] sel,
    output out
);

    // Define the shift register
    reg [2:0] shift_reg;
    always @(posedge clk) begin
        shift_reg[0] <= d;
        shift_reg[1] <= shift_reg[0];
        shift_reg[2] <= shift_reg[1];
    end

    // Define the multiplexer for the shift register
    wire [2:0] shift_mux_sel = {1'b0, sel[1:0]};
    wire shift_mux_out;
    assign shift_mux_out = shift_reg[shift_mux_sel];

    // Define the multiplexer for the password
    wire [7:0] password_mux_sel = {1'b0, sel[1:0]};
    wire [2:0] password_mux_out;
    assign password_mux_out = password[password_mux_sel];

    // Define the comparator
    wire [2:0] comparator_out;
    assign comparator_out = (shift_mux_out == password_mux_out);

    // Generate the shifted password
    wire [255:0] shifted_password = password;
    wire [2:0] constant_sel = 3'b0;
    wire [7:0] shifted_password_mux_sel = {1'b0, constant_sel[1:0]};
    wire [2:0] shifted_password_mux_out;
    assign shifted_password_mux_out = shifted_password[shifted_password_mux_sel];

    // Define the AND gate
    assign out = (comparator_out & shifted_password_mux_out);

endmodule
