// SVA for altera_up_video_camera_decoder
// Bind in your testbench: 
//   bind altera_up_video_camera_decoder altera_up_video_camera_decoder_sva #(.DW(DW)) u_sva(.*);

module altera_up_video_camera_decoder_sva #(parameter DW=9) (
  input logic                   clk,
  input logic                   reset,

  input logic [DW:0]            PIXEL_DATA,
  input logic                   LINE_VALID,
  input logic                   FRAME_VALID,
  input logic                   ready,

  input logic [DW:0]            data,
  input logic                   startofpacket,
  input logic                   endofpacket,
  input logic                   valid,

  // internal signals
  input logic                   read_temps,
  input logic [DW:0]            io_pixel_data,
  input logic                   io_line_valid,
  input logic                   io_frame_valid,
  input logic [DW:0]            temp_data,
  input logic                   temp_start,
  input logic                   temp_end,
  input logic                   temp_valid,
  input logic                   frame_sync
);

  // Equation of read_temps must hold every cycle
  assert property (@(posedge clk)
    read_temps == ((ready || !valid) && ((io_line_valid && io_frame_valid) || ((temp_start || temp_end) && temp_valid)))
  );

  // Reset state
  assert property (@(posedge clk)
    reset |=> (data=='0 && startofpacket==0 && endofpacket==0 && valid==0 &&
               frame_sync==0 && temp_data=='0 && temp_start==0 && temp_end==0 && temp_valid==0)
  );

  // Outputs update one cycle after read_temps (skid)
  assert property (@(posedge clk) disable iff (reset)
    read_temps |=> (data==$past(temp_data) &&
                    startofpacket==$past(temp_start) &&
                    endofpacket==$past(temp_end) &&
                    valid==$past(temp_valid))
  );

  // Temps capture io_ on read_temps
  assert property (@(posedge clk) disable iff (reset)
    read_temps |=> (temp_data==$past(io_pixel_data) &&
                    temp_start==$past(frame_sync) &&
                    temp_end==$past(!io_frame_valid) &&
                    temp_valid==$past(io_line_valid && io_frame_valid))
  );

  // temp_end must be set while frame invalid if not reading
  assert property (@(posedge clk) disable iff (reset)
    (!read_temps && !io_frame_valid) |=> temp_end
  );

  // frame_sync behavior
  assert property (@(posedge clk)
    reset |=> frame_sync==0
  );
  assert property (@(posedge clk) disable iff (reset)
    (!io_frame_valid) |=> frame_sync
  );
  assert property (@(posedge clk) disable iff (reset)
    (io_line_valid && io_frame_valid) |=> !frame_sync
  );

  // Data/SOP/EOP only change on read_temps
  assert property (@(posedge clk) disable iff (reset)
    $changed({data,startofpacket,endofpacket}) |-> $past(read_temps)
  );

  // Valid changes only due to prior read_temps or ready
  assert property (@(posedge clk) disable iff (reset)
    $changed(valid) |-> ($past(read_temps) || $past(ready))
  );

  // Valid deasserts on ready if no read_temps that cycle
  assert property (@(posedge clk) disable iff (reset)
    (!read_temps && ready) |=> !valid
  );

  // Hold behavior under backpressure (no read, no ready)
  assert property (@(posedge clk) disable iff (reset)
    (!read_temps && !ready) |=> ($stable(valid) && $stable({data,startofpacket,endofpacket}))
  );

  // SOP and EOP cannot both be 1 when valid
  assert property (@(posedge clk) disable iff (reset)
    valid |-> !(startofpacket && endofpacket)
  );

  // Coverage
  cover property (@(posedge clk) disable iff (reset)
    read_temps
  );
  cover property (@(posedge clk) disable iff (reset)
    (startofpacket && valid)
  );
  cover property (@(posedge clk) disable iff (reset)
    (endofpacket && valid)
  );
  cover property (@(posedge clk) disable iff (reset)
    (valid && !ready) ##1 (valid && !ready) // backpressure stretch
  );
  cover property (@(posedge clk) disable iff (reset)
    (startofpacket && valid) ##[1:$] (endofpacket && valid)
  );

endmodule

bind altera_up_video_camera_decoder
  altera_up_video_camera_decoder_sva #(.DW(DW)) u_altera_up_video_camera_decoder_sva(.*);