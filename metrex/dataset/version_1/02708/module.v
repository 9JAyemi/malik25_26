module niosII_system_switches (
                                // inputs:
                                 address,
                                 clk,
                                 in_port,
                                 reset_n,

                                // outputs:
                                 readdata
                              )
;

  output  [ 31: 0] readdata;
  input   [  1: 0] address;
  input            clk;
  input   [  7: 0] in_port;
  input            reset_n;

  wire             clk_en;
  wire    [  7: 0] data_in;
  wire    [  7: 0] read_mux_out;
  reg     [ 31: 0] readdata;
  assign clk_en = 1;
  
  //s1, which is an e_avalon_slave
  assign read_mux_out = {8 {(address == 0)}} & data_in;
  
  always @(posedge clk or negedge reset_n)
    begin
      if (reset_n == 0)
          readdata <= 0;
      else if (clk_en) begin
          case (address)
            2'b00: readdata <= {24'b0, data_in};
            2'b01: readdata <= {24'b0, data_in};
            2'b10: readdata <= {24'b0, data_in};
            2'b11: readdata <= {data_in, data_in, data_in, data_in};
            default: readdata <= 0;
          endcase
      end
    end

  assign data_in = in_port;

endmodule