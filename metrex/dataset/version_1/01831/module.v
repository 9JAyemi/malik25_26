module axi_traffic_gen_v2_0_7_id_track
        #(
parameter ID_WIDTH = 1
) (
  input                 Clk           ,
  input                 rst_l         ,
  input [ID_WIDTH-1:0]  in_push_id    ,
  input                 in_push       ,
  input [ID_WIDTH-1:0]  in_search_id  ,
  input [3:0]           in_clear_pos  ,
  input                 in_only_entry0,
  output [3:0]          out_push_pos  ,
  output [3:0]          out_search_hit,
  output [3:0]          out_free
);

// Declare registers to store the IDs
reg [ID_WIDTH:0] id_arr0_ff, id_arr1_ff, id_arr2_ff, id_arr3_ff;

// Declare registers to store the positions of the incoming transaction
reg [3:0] push_pos_ff, push_pos_2ff;

// Declare register to store the positions to be cleared
reg [3:0] in_clear_pos_ff;

// Create a wire to append a '1' to the incoming ID
wire [ID_WIDTH:0] push_id = { 1'b1, in_push_id[ID_WIDTH-1:0] };

// Create a wire to determine the positions of the incoming transaction
wire [3:0] push_search = { (push_id[ID_WIDTH:0] == id_arr3_ff[ID_WIDTH:0]),
                        (push_id[ID_WIDTH:0] == id_arr2_ff[ID_WIDTH:0]),
                        (push_id[ID_WIDTH:0] == id_arr1_ff[ID_WIDTH:0]),
                        (push_id[ID_WIDTH:0] == id_arr0_ff[ID_WIDTH:0]) };

// Create a wire to determine the positions of free slots
wire [3:0] free_pre = { ~id_arr3_ff[ID_WIDTH], ~id_arr2_ff[ID_WIDTH],
                        ~id_arr1_ff[ID_WIDTH], ~id_arr0_ff[ID_WIDTH] };
wire [3:0] free = (in_only_entry0) ? { 3'b000, free_pre[0] } : free_pre[3:0];
wire [3:0] first_free = (free[0]) ? 4'h1 :
                        (free[1]) ? 4'h2 :
                        (free[2]) ? 4'h4 :
                        (free[3]) ? 4'h8 : 4'h0;

// Create a wire to determine the position of the incoming transaction
wire [3:0] push_pos = (in_push == 1'b0) ? 4'h0 :
                (push_search[3:0] != 4'h0) ? push_search[3:0] :
                        first_free[3:0];

// Create a wire to append a '1' to the searched ID
wire [ID_WIDTH:0] search_id = { 1'b1, in_search_id[ID_WIDTH-1:0] };

// Create a wire to determine the position of the searched ID
wire [3:0] search_pos = { (search_id[ID_WIDTH:0] == id_arr3_ff[ID_WIDTH:0]),
                        (search_id[ID_WIDTH:0] == id_arr2_ff[ID_WIDTH:0]),
                        (search_id[ID_WIDTH:0] == id_arr1_ff[ID_WIDTH:0]),
                        (search_id[ID_WIDTH:0] == id_arr0_ff[ID_WIDTH:0]) };

// Create a wire to determine the positions to be cleared
wire [3:0] do_clear = ~push_pos_ff[3:0] & ~push_pos_2ff[3:0] &
                                                in_clear_pos_ff[3:0];

// Create wires to update the ID array
wire [ID_WIDTH:0] id_arr0 = (push_pos[0]) ? push_id[ID_WIDTH:0] :
        { (do_clear[0]) ? 1'b0:id_arr0_ff[ID_WIDTH], id_arr0_ff[ID_WIDTH-1:0] };
wire [ID_WIDTH:0] id_arr1 = (push_pos[1]) ? push_id[ID_WIDTH:0] :
        { (do_clear[1]) ? 1'b0:id_arr1_ff[ID_WIDTH], id_arr1_ff[ID_WIDTH-1:0] };
wire [ID_WIDTH:0] id_arr2 = (push_pos[2]) ? push_id[ID_WIDTH:0] :
        { (do_clear[2]) ? 1'b0:id_arr2_ff[ID_WIDTH], id_arr2_ff[ID_WIDTH-1:0] };
wire [ID_WIDTH:0] id_arr3 = (push_pos[3]) ? push_id[ID_WIDTH:0] :
        { (do_clear[3]) ? 1'b0:id_arr3_ff[ID_WIDTH], id_arr3_ff[ID_WIDTH-1:0] };

// Update the registers on the positive edge of the clock
always @(posedge Clk) begin
        id_arr0_ff[ID_WIDTH:0] <= (rst_l) ? id_arr0[ID_WIDTH:0] : 1'b0;
        id_arr1_ff[ID_WIDTH:0] <= (rst_l) ? id_arr1[ID_WIDTH:0] : 1'b0;
        id_arr2_ff[ID_WIDTH:0] <= (rst_l) ? id_arr2[ID_WIDTH:0] : 1'b0;
        id_arr3_ff[ID_WIDTH:0] <= (rst_l) ? id_arr3[ID_WIDTH:0] : 1'b0;
        push_pos_ff[3:0] <= (rst_l) ? push_pos[3:0] : 4'h0;
        push_pos_2ff[3:0] <= (rst_l) ? push_pos_ff[3:0] : 4'h0;
        in_clear_pos_ff[3:0] <= (rst_l) ? in_clear_pos[3:0] : 4'h0;
end

// Assign the output wires
assign out_search_hit[3:0] = search_pos[3:0];
assign out_push_pos[3:0] = push_pos[3:0];
assign out_free[3:0] = free[3:0];

endmodule