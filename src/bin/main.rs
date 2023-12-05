use inquire::InquireError;

fn main() -> Result<(), InquireError> {
    tracing_subscriber::fmt().init();
    tic_tac_toe_lib::game::Game::run()
}
