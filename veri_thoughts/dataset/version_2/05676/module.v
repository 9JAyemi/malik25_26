module dcf77_validy_checker #(parameter CLOCK_FREQUENCY = 16000000
			) ( 	
        input wire              clk,       	input wire              reset,          input wire [58:0] dcf_bits,
	input wire dcf_new_sec,

	output wire signal_valid
);  

  wire parity_min;
  wire parity_hour;
  wire parity_date;

  assign parity_min = (^dcf_bits[27:21] == dcf_bits[28]);
  assign parity_hour = (^dcf_bits[34:29] == dcf_bits[35]);
  assign parity_date = (^dcf_bits[57:36] == dcf_bits[58]);

  assign signal_valid = (parity_min && parity_hour && parity_date && (dcf_bits[0] == 1'b0) && (dcf_bits[20] == 1'b1) && dcf_new_sec);		

  endmodule