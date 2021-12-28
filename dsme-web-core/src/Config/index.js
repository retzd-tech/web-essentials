const {
    REACT_APP_MF_ONBOARDING_HOST: microOnboarding,
    REACT_APP_MF_ANGULAR_HOST: microAngular,
    REACT_APP_MF_DASHBOARD_HOST: microDashboard,
    REACT_APP_CONTENT_HOST: contentHost
} = process.env;

export default {
    microOnboarding,
    microAngular,
    microDashboard,
    contentHost
}