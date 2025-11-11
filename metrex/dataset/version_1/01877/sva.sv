// SVA for bluetooth_receiver
module bluetooth_receiver_sva (
  input logic         clk,
  input logic         reset,
  input logic [15:0]  rx_in,
  input logic [7:0]   data_out,
  input logic [15:0]  demodulated_data,
  input logic [7:0]   decoded_data,
  input logic [3:0]   bit_counter,
  input logic [15:0]  carrier_signal
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior (1-cycle later due to nonblocking assigns)
  assert property (reset |=> demodulated_data==16'h0 && carrier_signal==16'h0 &&
                            decoded_data==8'h0 && bit_counter==4'd0 &&
                            data_out==8'h0);

  // carrier_signal always shifts in rx_in[15]
  assert property (disable iff (reset)
    carrier_signal == { $past(carrier_signal)[14:0], $past(rx_in[15]) });

  // demodulated_data shifts only when rx_in[15] != previous carrier_signal[15]
  assert property (disable iff (reset)
    demodulated_data ==
      ( ($past(rx_in[15]) != $past(carrier_signal[15]))
        ? { $past(demodulated_data)[14:0], $past(rx_in[15]) }
        : $past(demodulated_data) ));

  // bit_counter counts 0->1->2->3->0
  assert property (disable iff (reset)
    bit_counter == ( $past(bit_counter)==4'd3 ? 4'd0 : $past(bit_counter)+4'd1 ));

  // decoded_data updates every time bit_counter was 3 (note 7-bit concat => MSB=0)
  assert property (disable iff (reset)
    decoded_data ==
      ( $past(bit_counter)==4'd3 ? {1'b0, $past(demodulated_data[6:0])}
                                 : $past(decoded_data) ));
  // MSB always 0 given 7-bit source
  assert property (disable iff (reset) decoded_data[7] == 1'b0);

  // data_out follows decoded_data by 1 cycle
  assert property (disable iff (reset) data_out == $past(decoded_data));

  // No X/Z after reset
  assert property (disable iff (reset)
    !$isunknown({carrier_signal, demodulated_data, decoded_data, bit_counter, data_out}));

  // Coverage
  cover property (disable iff (reset)
    ($past(rx_in[15]) != $past(carrier_signal[15])) ##1 $changed(demodulated_data)); // gated shift
  cover property (disable iff (reset)
    ($past(rx_in[15]) == $past(carrier_signal[15])) ##1 !$changed(demodulated_data)); // hold
  cover property (disable iff (reset)
    $past(bit_counter)==4'd3 ##1 (bit_counter==4'd0 &&
      decoded_data=={1'b0,$past(demodulated_data[6:0])})); // decode event
  cover property (disable iff (reset)
    $changed(decoded_data) ##1 data_out==$past(decoded_data)); // output follow
endmodule

// Bind into DUT
bind bluetooth_receiver bluetooth_receiver_sva u_bluetooth_receiver_sva (
  .clk(clk),
  .reset(reset),
  .rx_in(rx_in),
  .data_out(data_out),
  .demodulated_data(demodulated_data),
  .decoded_data(decoded_data),
  .bit_counter(bit_counter),
  .carrier_signal(carrier_signal)
);