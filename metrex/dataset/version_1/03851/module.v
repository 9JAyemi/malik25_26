
module data_mem (data_out,data_in,mem_ctrl_addr,clk,dm_ctrl_sig);

// Output signals...
output [0:127] data_out;

// Input signals
input [0:127] data_in;
input [0:31] mem_ctrl_addr;
input clk;
input [0:1] dm_ctrl_sig;

// Declare "reg" signals: 
reg [0:127] data_out;					// 128-bit register for data output
reg [0:127] data_mem [0:255];			// 256 x 128-bit memory array


// Read or write data based on control signal
always @(posedge clk) begin
    case (dm_ctrl_sig)
        2'b00: data_out <= data_mem[mem_ctrl_addr];
        2'b01: data_mem[mem_ctrl_addr] <= data_in;
        default: data_out <= 128'd0;
    endcase
end

endmodule
