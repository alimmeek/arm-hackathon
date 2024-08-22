module arbiter (
    input  logic clk,
    input  logic resetn,

    input  logic [2:0] r,   // Resource request from each device
    
    output logic [2:0] g    // Status of grants
);

// State machine encoding
parameter A = 2'b00, B = 2'b01, C = 2'b10, D = 2'b11;

logic [1:0] next_state;
logic [1:0] curr_state;

logic [2:0] g_next;
logic [2:0] g_q;


// Decide next state based on current state and which devices (if any) have requested the resource
always_comb begin
    next_state = curr_state;

    case (curr_state)
        A : begin
            if (r[0]) begin
                next_state = B;
            end else if (r[1]) begin
                next_state = C;
            end else if (r[2]) begin
                next_state = D;
            end
        end

        B : begin
            if (~r[0]) begin
                next_state = A;
            end
        end

        C : begin
            if (~r[1]) begin
                next_state = A;
            end
        end

        D : begin
            if (~r[2]) begin
                next_state = A;
            end
        end
    endcase
end

// Allocate resource based on current state
always_comb begin
    g_next = g_q;

    // Use next_state to reduce latency between a state changing and the resource being allocated
    case (next_state)
        A : g_next = 3'b000;

        B : g_next = 3'b001;

        C : g_next = 3'b010;

        D : g_next = 3'b100;
    endcase
end

// Update the current state and grant on each clock cycle
// On resetn, set the state machine to state A and deallocate the resource
always_ff @(posedge clk or negedge resetn) begin
    if (~resetn) begin
        curr_state <= A;
        g_q <= 3'b000;
    end else begin
        curr_state <= next_state;
        g_q <= g_next;
    end
end

assign g = g_q;



// Assertions

default clocking @(posedge clk);
endclocking

assert_a_to_b : assert property (((r[0]) && (curr_state == A)) |-> ##1 (curr_state == B));    // Whenever device 1 is requesting, allocate to device 1

assert_a_to_c : assert property (((r[1] && ~r[0]) && (curr_state == A)) |-> ##1 (curr_state == C));    // If device 1 isn't requesting and device 2 is, allocate to device 2

assert_a_to_d : assert property (((r[2]&& ~r[0] && ~r[1]) && (curr_state == A)) |-> ##1 (curr_state == D));    // If only device 3 is requesting, allocate to device 3

assert_b_to_a : assert property (((~r[0]) && (curr_state == B)) |-> ##1 (curr_state == A));    // State should move back to A when device 1 stops requesting

assert_c_to_a : assert property (((~r[1]) && (curr_state == C)) |-> ##1 (curr_state == A));    // State should move back to A when device 2 stops requesting

assert_d_to_a : assert property (((~r[2]) && (curr_state == D)) |-> ##1 (curr_state == A));    // State should move back to A when device 3 stops requesting

assert_b_cant_go_to_c_or_d : assert property ((curr_state == B) |-> ((next_state != C) && (next_state != D)));    // Check for illegal transitions from state B

assert_c_cant_go_to_b_or_d : assert property ((curr_state == C) |-> ((next_state != B) && (next_state != D)));    // Check for illegal transitions from state C

assert_d_cant_go_to_b_or_c : assert property ((curr_state == D) |-> ((next_state != B) && (next_state != C)));    // Check for illegal transitions from state D

assert_g0_gets_set : assert property ((next_state == B) |-> ##1 (g[0] == 1'b1));    // Resource should be allocated to device 1 when in state B

assert_g1_gets_set : assert property ((next_state == C) |-> ##1 (g[1] == 1'b1));    // Resource should be allocated to device 2 when in state C

assert_g2_gets_set : assert property ((next_state == D) |-> ##1 (g[2] == 1'b1));    // Resource should be allocated to device 3 when in state D

assert_only_one_granted : assert property ($onehot(g_q) || g_q == 3'b0);    // At most 1 device should have the resource

endmodule