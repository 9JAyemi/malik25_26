module RAM_SHIFTER #(
    parameter IO_WIDTH = 16,
    parameter ADDR_WIDTH = 4,
    parameter PHASE_SHIFT = 2
) (
    input                       clk,

    input [IO_WIDTH-1:0]        in,
    output reg [IO_WIDTH-1:0]   out,

    output reg [ADDR_WIDTH-1:0] addr,
    input                       ram_out,
    output                      ram_in
);

    reg [IO_WIDTH-1:0]          shift_in;
    reg [IO_WIDTH-1:0]          shift_out;

    assign ram_in = shift_in[0];

    initial begin
        out       <= 0;
        addr      <= 0;
        shift_in  <= 0;
        shift_out <= 0;
    end

    always @(posedge clk) begin
        if(addr == 0)
          begin out <= {shift_out[IO_WIDTH-PHASE_SHIFT-1:0], shift_out[IO_WIDTH-1:IO_WIDTH-PHASE_SHIFT]};

              shift_in <= in;
          end
        else
          begin
              shift_in <= {shift_in[IO_WIDTH-2:0], shift_in[IO_WIDTH-1]};
          end

        shift_out <= {shift_out[IO_WIDTH-2:0], ram_out};

        addr <= addr + 1;
    end
endmodule
