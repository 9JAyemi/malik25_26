module ssio_sdr_in_sva (
    input logic input_clk,
    input logic [WIDTH-1:0] input_d,
    output logic output_clk,
    output logic [WIDTH-1:0] output_q
);
    // Clock and reset signals
    logic clk_int;
    logic clk_io;
    logic resetn;

    // Generate block to handle different clock input styles
    generate
        if (CLOCK_INPUT_STYLE == "BUFG") begin
            BUFG
            clk_bufg (
                .I(input_clk),
                .O(clk_int)
            );
            assign clk_io = clk_int;
            assign output_clk = clk_int;
        end else if (CLOCK_INPUT_STYLE == "BUFR") begin
            assign clk_int = input_clk;
            BUFIO
            clk_bufio (
                .I(clk_int),
                .O(clk_io)
            );
            BUFR #(
                .BUFR_DIVIDE("BYPASS")
            )
            clk_bufr (
                .I(clk_int),
                .O(output_clk),
                .CE(1'b1),
                .CLR(1'b0)
            );
        end else if (CLOCK_INPUT_STYLE == "BUFIO") begin
            assign clk_int = input_clk;
            BUFIO
            clk_bufio (
                .I(clk_int),
                .O(clk_io)
            );
            BUFG
            clk_bufg (
                .I(clk_int),
                .O(output_clk)
            );
        end else if (CLOCK_INPUT_STYLE == "BUFIO2") begin
            BUFIO2 #(
                .DIVIDE(1),
                .DIVIDE_BYPASS("TRUE"),
                .I_INVERT("FALSE"),
                .USE_DOUBLER("FALSE")
            )
            clk_bufio (
                .I(input_clk),
                .DIVCLK(clk_int),
                .IOCLK(clk_io),
                .SERDESSTROBE()
            );
            BUFG
            clk_bufg (
                .I(clk_int),
                .O(output_clk)
            );
        end
    endgenerate

    // Assign resetn based on the reset signal
    assign resetn = !reset;

    // Sequential logic
    reg [WIDTH-1:0] output_q_reg = {WIDTH{1'b0}};

    always @(posedge clk_io) begin
        output_q_reg <= input_d;
    end

    // Assertions
    // Output_q_reg should always be equal to input_d at the rising edge of clk_io
    property p_output_q_reg;
        @(posedge clk_io) disable iff (!resetn) output_q_reg == input_d;
    endproperty
    a_output_q_reg: assert property (p_output_q_reg) else $error("Output_q_reg is not equal to input_d at the rising edge of clk_io");

    // Output_clk should always be equal to clk_io
    property p_output_clk;
        @(posedge clk_io) disable iff (!resetn) output_clk == clk_io;
    endproperty
    a_output_clk: assert property (p_output_clk) else $error("Output_clk is not equal to clk_io");

    // clk_int should always be equal to input_clk
    property p_clk_int;
        @(posedge clk_io) disable iff (!resetn) clk_int == input_clk;
    endproperty
    a_clk_int: assert property (p_clk_int) else $error("clk_int is not equal to input_clk");

    // clk_io should always be equal to clk_int
    property p_clk_io;
        @(posedge clk_io) disable iff (!resetn) clk_io == clk_int;
    endproperty
    a_clk_io: assert property (p_clk_io) else $error("clk_io is not equal to clk_int");

    // output_q should always be equal to output_q_reg
    property p_output_q;
        @(posedge clk_io) disable iff (!resetn) output_q == output_q_reg;
    endproperty
    a_output_q: assert property (p_output_q) else $error("output_q is not equal to output_q_reg");

    // input_d should always be a valid input
    property p_input_d;
        @(posedge clk_io) disable iff (!resetn) input_d inside {[0:255]};
    endproperty
    a_input_d: assert property (p_input_d) else $error("input_d is not a valid input");

    // clk_io should always be a valid clock
    property p_clk_io_valid;
        @(posedge clk_io) disable iff (!resetn) clk_io;
    endproperty
    a_clk_io_valid: assert property (p_clk_io_valid) else $error("clk_io is not a valid clock");

    // clk_int should always be a valid clock
    property p_clk_int_valid;
        @(posedge clk_io) disable iff (!resetn) clk_int;
    endproperty
    a_clk_int_valid: assert property (p_clk_int_valid) else $error("clk_int is not a valid clock");

    // output_clk should always be a valid clock
    property p_output_clk_valid;
        @(posedge clk_io) disable iff (!resetn) output_clk;
    endproperty
    a_output_clk_valid: assert property (p_output_clk_valid) else $error("output_clk is not a valid clock");

    // output_q_reg should always be a valid output
    property p_output_q_reg_valid;
        @(posedge clk_io) disable iff (!resetn) output_q_reg inside {[0:255]};
    endproperty
    a_output_q_reg_valid: assert property (p_output_q_reg_valid) else $error("output_q_reg is not a valid output");

    // output_q should always be a valid output
    property p_output_q_valid;
        @(posedge clk_io) disable iff (!resetn) output_q inside {[0:255]};
    endproperty
    a_output_q_valid: assert property (p_output_q_valid) else $error("output_q is not a valid output");
endmodule